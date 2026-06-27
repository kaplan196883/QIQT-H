/-
Copyright (c) 2026 PK. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.

# The continuum Stone exponential `U_t = exp(it A)` via the Cayley transform

Split out of `QIQTH/Spectral/Garding.lean` (which grew to ~2600 lines and made per-edit recompiles slow).
This module is the **Stone-exponential layer**.  It builds on everything in `Garding.lean`: the Cayley unitary
`V = cayleyUnitary U`, its finite scalar spectral measures `μ_x = cayleyScalarMeasure`, the CFC↔measure
dictionary (`cayley_cfc_norm_sq_integral`, `cayley_cfc_sub_norm_sq_integral`), the L²→strong-operator bridge
(`cayley_cfc_tendsto_zero_of_integral`, `cayley_cfc_cauchySeq_of_integral`), and the atom-killing
`cayleyScalarMeasure_atom_eq_zero : μ_x ({1}) = 0`.

Here we define:
* `cayleyInv ω = i(1+ω)/(1−ω)` — the inverse-Cayley map; real on `σ(V) \ {1}` (`cayleyInv_im_eq_zero`), i.e.
  the spectral value of the self-adjoint generator `A` with `cayleyUnitary` Cayley transform `V`;
* `cayleyExp t ω = exp(it · cayleyInv ω)` — the Stone-exponential symbol; modulus `1` on the circle, group law
  `e_0 = 1`, `e_s · e_t = e_{s+t}`;
* `cayleyBump`, `cayleyExpBump` — continuous cutoffs `g_{t,N} = e_t · η_N` approximating `e_t` in L²(μ_x);
* `cayleyStoneU U t x = lim_N cfc (g_{t,N}) V x` — the **continuum Stone exponential** `U_t = exp(it A)`,
  defined as a strong limit (no PVM), and shown ℂ-linear (`cayleyStoneU_add`, `cayleyStoneU_smul`).

All declarations are axiom-free (standard `propext` / `Classical.choice` / `Quot.sound` only), budget 0.
-/
import QIQTH.Spectral.Garding

namespace QIQTH.Spectral

open MeasureTheory
open scoped CompactlySupported
open CompactlySupportedContinuousMap

section SelfAdjoint
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- The CFC instance for the normal Cayley unitary `V` (needs `[Nontrivial H]`); re-declared as a local instance
-- here because the corresponding `attribute [local instance]` in `Garding.lean` does not propagate to importers.
attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-- **The inverse Cayley map** `c(ω) = i(1 + ω)/(1 − ω)` on `ℂ \ {1}`.  It is the inverse of the Cayley transform
    `z ↦ (z − i)/(z + i)`: on the unit circle (minus the excluded point `1`, the image of `∞`) it returns the
    **real** spectral value of the self-adjoint generator `A = i(1 + V)(1 − V)⁻¹` whose Cayley transform is `V`.
    The Stone-exponential symbol is `ω ↦ exp(it · c(ω))`; since `c` is real on `σ(V) \ {1}` (`cayleyInv_im_eq_zero`)
    that symbol has modulus `1`, and since `μ_x({1}) = 0` (`cayleyScalarMeasure_atom_eq_zero`) it is `μ_x`-a.e.
    defined and bounded — the data the strong-limit Stone exponential `U_t = exp(it A)` consumes. -/
noncomputable def cayleyInv (ω : ℂ) : ℂ := Complex.I * (1 + ω) / (1 - ω)

/-- The inverse Cayley map is continuous off the excluded point `1` (the denominator `1 − ω` is nonzero there). -/
theorem cayleyInv_continuousOn : ContinuousOn cayleyInv {ω : ℂ | ω ≠ 1} :=
  (continuous_const.mul (continuous_const.add continuous_id)).continuousOn.div
    (continuous_const.sub continuous_id).continuousOn
    (fun _ hω => sub_ne_zero.mpr (Ne.symm hω))

/-- **The inverse Cayley map is real on the unit circle** (off `1`): `(c(ω)).im = 0` for `‖ω‖ = 1`, `ω ≠ 1`.
    This is the statement that the generator `A = i(1 + V)(1 − V)⁻¹` is **self-adjoint** (its spectral values are
    real), so the Stone-exponential symbol `exp(it · c(ω))` has modulus `1` (hence `U_t` is unitary).  Proof: on
    the circle `conj ω = ω⁻¹` (`RCLike.inv_eq_conj`), and a direct computation gives `conj(c(ω)) = c(ω)`
    (`field_simp`/`ring`), i.e. `c(ω)` is real. -/
theorem cayleyInv_im_eq_zero {ω : ℂ} (h1 : ‖ω‖ = 1) (hne : ω ≠ 1) : (cayleyInv ω).im = 0 := by
  have hcc : ω * (starRingEnd ℂ) ω = 1 := by rw [RCLike.mul_conj, h1]; norm_num
  have hd1 : (1 : ℂ) - ω ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hd2 : (1 : ℂ) - (starRingEnd ℂ) ω ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    apply hne
    have : (starRingEnd ℂ) ((starRingEnd ℂ) ω) = (starRingEnd ℂ) 1 := congrArg _ h.symm
    simpa using this
  rw [← Complex.conj_eq_iff_im]
  simp only [cayleyInv, map_div₀, map_mul, map_add, map_sub, map_one, Complex.conj_I]
  rw [div_eq_div_iff hd2 hd1]
  linear_combination (2 * Complex.I) * hcc

/-- **The Stone-exponential symbol** `e_t(ω) = exp(i · t · c(ω))`, where `c = cayleyInv`.  This is the bounded Borel
    function whose functional calculus `cfc(e_t) V` *is* the Stone unitary `U_t = exp(it A)` of the self-adjoint
    generator `A = i(1 + V)(1 − V)⁻¹` (`A = cayleyInv(V)`).  It is continuous off the excluded point `1`
    (`cayleyExp_continuousOn`) and has **modulus `1`** on the unit circle off `1` (`cayleyExp_abs`, since `c` is real
    there) — so it is bounded.  Because `μ_x({1}) = 0` (`cayleyScalarMeasure_atom_eq_zero`) it is `μ_x`-a.e.
    continuous and bounded, hence approximable in `L²(μ_x)` by continuous functions, whose cfc-vectors converge
    (the L²→strong bridge) to define `U_t x` as a strong limit — the genuine continuum Stone exponential. -/
noncomputable def cayleyExp (t : ℝ) (ω : ℂ) : ℂ := Complex.exp (Complex.I * ((t : ℂ) * cayleyInv ω))

/-- The Stone-exponential symbol is continuous off the excluded point `1` (`exp` ∘ a function continuous there). -/
theorem cayleyExp_continuousOn (t : ℝ) : ContinuousOn (cayleyExp t) {ω : ℂ | ω ≠ 1} :=
  Complex.continuous_exp.comp_continuousOn
    ((cayleyInv_continuousOn.const_mul (t : ℂ)).const_mul Complex.I)

/-- **The Stone-exponential symbol has modulus `1` on the unit circle** (off `1`): `‖e_t(ω)‖ = 1` for `‖ω‖ = 1`,
    `ω ≠ 1`.  Since `c(ω)` is real there (`cayleyInv_im_eq_zero`), `i · t · c(ω)` is purely imaginary, so
    `‖exp(i t c(ω))‖ = exp((i t c(ω)).re) = exp(0) = 1` (`Complex.norm_exp`).  This is the unitarity of the Stone
    exponential `U_t = cfc(e_t) V` and the boundedness that makes `e_t ∈ L²(μ_x)`. -/
theorem cayleyExp_abs {t : ℝ} {ω : ℂ} (h1 : ‖ω‖ = 1) (hne : ω ≠ 1) : ‖cayleyExp t ω‖ = 1 := by
  have hc : (cayleyInv ω).im = 0 := cayleyInv_im_eq_zero h1 hne
  have him : (Complex.I * ((t : ℂ) * cayleyInv ω)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, hc]
  rw [cayleyExp, Complex.norm_exp, him, Real.exp_zero]

/-- **The Stone-exponential symbol at `t = 0` is the constant `1`:** `e_0(ω) = 1` (`exp 0 = 1`).  The symbol-level
    seed of `U_0 = cfc(e_0) V = cfc 1 V = 1` — the identity element of the one-parameter unitary group. -/
theorem cayleyExp_zero (ω : ℂ) : cayleyExp 0 ω = 1 := by
  simp [cayleyExp]

/-- **The one-parameter group law of the Stone-exponential symbol:** `e_s(ω) · e_t(ω) = e_{s+t}(ω)`.  Immediate
    from `exp` (`Complex.exp_add`): `exp(i s c)·exp(i t c) = exp(i(s+t)c)`.  This is the symbol-level seed of the
    **one-parameter unitary group law** `U_s U_t = U_{s+t}` (`cfc(e_s) V · cfc(e_t) V = cfc(e_s·e_t) V =
    cfc(e_{s+t}) V`, by multiplicativity of the functional calculus), one of the two Stone-group axioms (with
    `cayleyExp_zero`); strong continuity `t ↦ U_t x` is the third. -/
theorem cayleyExp_add (s t : ℝ) (ω : ℂ) : cayleyExp s ω * cayleyExp t ω = cayleyExp (s + t) ω := by
  rw [cayleyExp, cayleyExp, cayleyExp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The continuous bump cutoff** `η_N(ω) = 1 − ψ_N(ω)`, complementary to the rational cutoff `cayleyCutoff`.
    As `N → ∞` it rises to the indicator of `ℂ \ {1}`: `η_N(1) = 0` for all `N` (so it vanishes at the Cayley
    exceptional point, taming the symbol's discontinuity there), while `η_N(ω) → 1` for `ω ≠ 1`.  Each `η_N` is
    continuous and valued in `[0, 1]`.  The cutoff symbol `e_t · η_N` is then **continuous on `σ(V)`** (`η_N → 0`
    kills `e_t`'s discontinuity at `1`) and converges to `e_t` in `L²(μ_x)` (since `μ_x({1}) = 0`), so its
    cfc-vectors converge to define the Stone unitary `U_t x = lim cfc(e_t · η_N) V x`. -/
noncomputable def cayleyBump (N : ℕ) (ω : ℂ) : ℝ := 1 - cayleyCutoff N ω

/-- Each bump `η_N` is continuous on `ℂ` (`1 −` a continuous function). -/
theorem cayleyBump_continuous (N : ℕ) : Continuous (cayleyBump N) :=
  continuous_const.sub (cayleyCutoff_continuous N)

/-- The bump is nonnegative (`ψ_N ≤ 1`). -/
theorem cayleyBump_nonneg (N : ℕ) (ω : ℂ) : 0 ≤ cayleyBump N ω :=
  sub_nonneg.mpr (cayleyCutoff_le_one N ω)

/-- The bump is bounded by `1` (`0 < ψ_N`); so `η_N ∈ [0, 1]` is an integrable DCT dominator. -/
theorem cayleyBump_le_one (N : ℕ) (ω : ℂ) : cayleyBump N ω ≤ 1 := by
  have := (cayleyCutoff_pos N ω).le
  simp only [cayleyBump]; linarith

/-- **The pointwise limit of the bump sequence is the indicator of `ℂ \ {1}`:**
    `η_N(ω) → (if ω = 1 then 0 else 1)`.  Complementary to `cayleyCutoff_tendsto_indicator` (`ψ_N → 1_{ω=1}`):
    `η_N = 1 − ψ_N → 1 − 1_{ω=1}`.  This is the convergence DCT consumes to show `e_t · η_N → e_t` in `L²(μ_x)`. -/
theorem cayleyBump_tendsto_indicator (ω : ℂ) :
    Filter.Tendsto (fun N => cayleyBump N ω) Filter.atTop
      (nhds (if ω = 1 then (0 : ℝ) else 1)) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (cayleyCutoff_tendsto_indicator ω)
  have heq : (1 : ℝ) - (if ω = 1 then (1 : ℝ) else 0) = (if ω = 1 then (0 : ℝ) else 1) := by
    by_cases hω : ω = 1 <;> simp [hω]
  rw [heq] at h
  exact h

/-- **The Stone-exponential symbol has modulus `1` on the *whole* unit circle**, including the excluded point `1`:
    `‖e_t(ω)‖ = 1` for `‖ω‖ = 1`.  At `ω ≠ 1` this is `cayleyExp_abs`; at `ω = 1` the junk value
    `cayleyInv 1 = i·2/0 = 0` gives `e_t(1) = exp 0 = 1`, of modulus `1`.  So `‖e_t‖ = 1` on all of `σ(V) ⊆ S¹` —
    the uniform bound that makes the cutoff symbol `e_t · η_N` an `L²(μ_x)` approximant of `e_t`. -/
theorem cayleyExp_abs_circle {t : ℝ} {ω : ℂ} (h1 : ‖ω‖ = 1) : ‖cayleyExp t ω‖ = 1 := by
  by_cases hne : ω = 1
  · subst hne; simp [cayleyExp, cayleyInv]
  · exact cayleyExp_abs h1 hne

/-- **The pointwise `L²`-defect of the cutoff symbol on the circle:** `‖e_t(ω)·η_N(ω) − e_t(ω)‖ = ψ_N(ω)` for
    `‖ω‖ = 1`.  Since `e_t·η_N − e_t = e_t·(η_N − 1)` and `‖e_t‖ = 1` on the circle (`cayleyExp_abs_circle`),
    `‖e_t·(η_N − 1)‖ = |η_N − 1| = |−ψ_N| = ψ_N` (`η_N = 1 − ψ_N`, `ψ_N ≥ 0`).  Hence `‖e_t·η_N − e_t‖² = ψ_N²`,
    which `→ 0` in `L²(μ_x)` (since `∫ ψ_N² dμ_x ≤ ∫ ψ_N dμ_x → μ_x({1}) = 0`): the cutoff symbol converges to the
    symbol in `L²(μ_x)`, the input to the strong-limit definition of `U_t`. -/
theorem cayleyExpBump_sub_norm (t : ℝ) (N : ℕ) {ω : ℂ} (h1 : ‖ω‖ = 1) :
    ‖cayleyExp t ω * (cayleyBump N ω : ℂ) - cayleyExp t ω‖ = cayleyCutoff N ω := by
  have habs : ‖cayleyExp t ω‖ = 1 := cayleyExp_abs_circle h1
  have hfac : cayleyExp t ω * (cayleyBump N ω : ℂ) - cayleyExp t ω
      = cayleyExp t ω * (((cayleyBump N ω - 1 : ℝ)) : ℂ) := by push_cast; ring
  rw [hfac, norm_mul, habs, one_mul, Complex.norm_real, cayleyBump,
    show (1 - cayleyCutoff N ω - 1 : ℝ) = -cayleyCutoff N ω by ring,
    Real.norm_eq_abs, abs_neg, abs_of_nonneg (cayleyCutoff_pos N ω).le]

/-- **`∫ ψ_N² dμ_x → 0`** — the squeeze closing the atom-killing into an `L²` statement.  Since `0 ≤ ψ_N ≤ 1`,
    `ψ_N² ≤ ψ_N`, so `0 ≤ ∫ ψ_N² ≤ ∫ ψ_N` (`integral_mono_of_nonneg`); and `∫ ψ_N dμ_x → μ_x({1}) = 0` (DCT-1
    `cayleyCutoff_integral_tendsto_atom` + the atom-killing `cayleyScalarMeasure_atom_eq_zero`).  By the squeeze
    `∫ ψ_N² dμ_x → 0`.  This is the `L²(μ_x)`-defect of the cutoff symbol (`cayleyExpBump_sub_norm`: `‖g−e_t‖² = ψ_N²`),
    so it gives the `L²` convergence `g_{t,N} → e_t`. -/
theorem cayleyCutoff_sq_integral_tendsto_zero [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H) :
    Filter.Tendsto
      (fun N => ∫ ω, (cayleyCutoff N (ω : ℂ)) ^ 2 ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))
      Filter.atTop (nhds 0) := by
  haveI : IsFiniteMeasure (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) :=
    cayleyScalarMeasure_isFiniteMeasure U hgrp hU0 hUinner hUbd hSC x
  have hint : ∀ N, Integrable
      (fun ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) => cayleyCutoff N (ω : ℂ))
      (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := by
    intro N
    refine (integrable_const (1 : ℝ)).mono' ?_ ?_
    · exact ((cayleyCutoff_continuous N).comp continuous_subtype_val).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_of_nonneg (cayleyCutoff_pos N _).le]; exact cayleyCutoff_le_one N _
  have hatom := cayleyCutoff_integral_tendsto_atom U hgrp hU0 hUinner hUbd hSC x
  rw [cayleyScalarMeasure_atom_eq_zero U hgrp hU0 hUinner hUbd hSC x, ENNReal.toReal_zero] at hatom
  refine squeeze_zero (fun N => integral_nonneg (fun ω => sq_nonneg _)) (fun N => ?_) hatom
  apply integral_mono_of_nonneg
  · exact Filter.Eventually.of_forall (fun ω => sq_nonneg _)
  · exact hint N
  · filter_upwards with ω
    nlinarith [(cayleyCutoff_pos N (ω : ℂ)).le, cayleyCutoff_le_one N (ω : ℂ)]

/-- **★★ The cutoff symbol converges to the symbol in `L²(μ_x)`:**
    `∫ ‖e_t·η_N − e_t‖² dμ_x → 0`.  By `cayleyExpBump_sub_norm` the integrand is `ψ_N(ω.1)²` on `σ(V) ⊆ S¹`
    (`integral_congr_ae`), so this is `cayleyCutoff_sq_integral_tendsto_zero` (`∫ ψ_N² → 0`).  Combined with the
    `L²`-distance Parseval, it gives the `L²(μ_x)`-Cauchy condition for `cfc(e_t·η_N) V x`, whose strong limit is
    the Stone unitary `U_t x = lim cfc(e_t·η_N) V x`.  Axiom-free; free scalar; no UV datum. -/
theorem cayleyExpBump_L2_tendsto_zero [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (t : ℝ) (x : H) :
    Filter.Tendsto
      (fun N => ∫ ω, ‖cayleyExp t (ω : ℂ) * (cayleyBump N (ω : ℂ) : ℂ) - cayleyExp t (ω : ℂ)‖ ^ 2
        ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))
      Filter.atTop (nhds 0) := by
  have heq : ∀ N, (∫ ω, ‖cayleyExp t (ω : ℂ) * (cayleyBump N (ω : ℂ) : ℂ) - cayleyExp t (ω : ℂ)‖ ^ 2
        ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))
      = ∫ ω, (cayleyCutoff N (ω : ℂ)) ^ 2 ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := by
    intro N
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
    have hcirc : ‖(ω : ℂ)‖ = 1 := by
      have hmem := cayley_spectrum_subset_circle U hgrp hU0 hUinner hUbd hSC ω.2
      rwa [mem_sphere_zero_iff_norm] at hmem
    show ‖cayleyExp t (ω : ℂ) * (cayleyBump N (ω : ℂ) : ℂ) - cayleyExp t (ω : ℂ)‖ ^ 2
      = (cayleyCutoff N (ω : ℂ)) ^ 2
    rw [cayleyExpBump_sub_norm t N hcirc]
  simp only [heq]
  exact cayleyCutoff_sq_integral_tendsto_zero U hgrp hU0 hUinner hUbd hSC x

/-- **The cutoff Stone-exponential symbol** `g_{t,N}(ω) = e_t(ω) · η_N(ω)` — the continuous approximant of the symbol
    `e_t`, with the bump `η_N` taming `e_t`'s discontinuity at the excluded point `1` (`η_N(1) = 0`).  Its cfc
    `cfc(g_{t,N}) V x` is a continuous-function functional-calculus vector; as `N → ∞` these converge (the L²→strong
    bridge, since `g_{t,N} → e_t` in `L²(μ_x)`) to define the Stone unitary `U_t x = lim cfc(g_{t,N}) V x`. -/
noncomputable def cayleyExpBump (t : ℝ) (N : ℕ) (ω : ℂ) : ℂ := cayleyExp t ω * (cayleyBump N ω : ℂ)

/-- The cutoff symbol has norm `η_N` on the unit circle: `‖g_{t,N}(ω)‖ = η_N(ω)` for `‖ω‖ = 1` (`‖e_t‖ = 1`,
    `η_N ≥ 0`).  This is the squeeze that gives `g_{t,N}` continuity at the excluded point `1` (`‖g‖ = η_N → 0`). -/
theorem cayleyExpBump_norm (t : ℝ) (N : ℕ) {ω : ℂ} (h1 : ‖ω‖ = 1) :
    ‖cayleyExpBump t N ω‖ = cayleyBump N ω := by
  rw [cayleyExpBump, norm_mul, cayleyExp_abs_circle h1, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (cayleyBump_nonneg N ω)]

/-- **★★ The cutoff symbol is continuous on `σ(V)`:** `ContinuousOn (g_{t,N}) (spectrum ℂ V)`.  Off the excluded
    point `1` it is a product of continuous functions (`cayleyExp_continuousOn`, `cayleyBump_continuous`); at `1`
    (if `1 ∈ σ(V)`) the value is `g_{t,N}(1) = e_t(1)·0 = 0`, and `‖g_{t,N}(ω)‖ = η_N(ω) → η_N(1) = 0`
    (`cayleyExpBump_norm` on `σ(V) ⊆ S¹` + `η_N` continuous) — the squeeze giving `ContinuousWithinAt` at `1`.
    So `cfc(g_{t,N}) V` is well-defined (the cfc needs `ContinuousOn (σ(V))`), the operator whose strong limit is
    `U_t`.  Axiom-free; free scalar; no UV datum. -/
theorem cayleyExpBump_continuousOn [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (t : ℝ) (N : ℕ) :
    ContinuousOn (cayleyExpBump t N)
      (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) := by
  intro ω hω
  by_cases hne : ω = 1
  · -- at the excluded point: the norm squeeze ‖g‖ = η_N → 0
    subst hne
    have hg1 : cayleyExpBump t N 1 = 0 := by simp [cayleyExpBump, cayleyBump, cayleyCutoff]
    rw [ContinuousWithinAt, hg1, tendsto_zero_iff_norm_tendsto_zero]
    have heqon : Set.EqOn (fun ω => ‖cayleyExpBump t N ω‖) (cayleyBump N)
        (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) := by
      intro ω hωs
      have hc : ‖ω‖ = 1 := by
        have hmem := cayley_spectrum_subset_circle U hgrp hU0 hUinner hUbd hSC hωs
        rwa [mem_sphere_zero_iff_norm] at hmem
      exact cayleyExpBump_norm t N hc
    refine Filter.Tendsto.congr' (eventuallyEq_nhdsWithin_of_eqOn heqon.symm) ?_
    have hb1 : cayleyBump N 1 = 0 := by simp [cayleyBump, cayleyCutoff]
    rw [← hb1]
    exact (cayleyBump_continuous N).continuousWithinAt
  · -- off the excluded point: product of continuous-at functions
    have he : ContinuousAt (cayleyExp t) ω :=
      (cayleyExp_continuousOn t).continuousAt (isOpen_ne.mem_nhds hne)
    have hb : ContinuousAt (fun z => (cayleyBump N z : ℂ)) ω :=
      (Complex.continuous_ofReal.comp (cayleyBump_continuous N)).continuousAt
    exact (he.mul hb).continuousWithinAt

/-- **★★★ The cutoff Stone-exponential cfc vectors form a Cauchy sequence:** `cfc(g_{t,N}) V x` is a `CauchySeq`
    in `H` (hence converges, `H` complete) — whose **strong limit is the Stone unitary `U_t x`**.  The cutoff
    symbol `g_{t,N} = e_t·η_N` is `ContinuousOn σ(V)` (`cayleyExpBump_continuousOn`, so the cfc applies) and converges
    to `e_t` in `L²(μ_x)` (`cayleyExpBump_L2_tendsto_zero`); an `L²(μ_x)`-convergent sequence is `L²`-Cauchy (the
    quadratic triangle `‖g_m − g_n‖² ≤ 2‖g_m − e_t‖² + 2‖g_n − e_t‖²` with `c = e_t`, integrated via
    `integral_mono_of_nonneg`), so `cayley_cfc_cauchySeq_of_integral` (the existence half of the L²→strong bridge)
    yields the `CauchySeq`.  This is the construction of the continuum Stone exponential `U_t = exp(it A)` as a strong
    limit of continuous functional calculi, with NO projection-valued measure.  Axiom-free; free scalar; no UV datum. -/
theorem cayleyExpBump_cfc_cauchySeq [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (t : ℝ) (x : H) :
    CauchySeq (fun N => cfc (cayleyExpBump t N)
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x) := by
  haveI : IsFiniteMeasure (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) :=
    cayleyScalarMeasure_isFiniteMeasure U hgrp hU0 hUinner hUbd hSC x
  -- each ‖g_N − e_t‖² is integrable (a.e. equal to ψ_N², which is continuous and bounded)
  have hint : ∀ N, Integrable
      (fun ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) =>
        ‖cayleyExp t (ω : ℂ) * (cayleyBump N (ω : ℂ) : ℂ) - cayleyExp t (ω : ℂ)‖ ^ 2)
      (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := by
    intro N
    have hψint : Integrable
        (fun ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) =>
          (cayleyCutoff N (ω : ℂ)) ^ 2) (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := by
      refine (integrable_const (1 : ℝ)).mono' ?_ ?_
      · exact (((cayleyCutoff_continuous N).comp continuous_subtype_val).pow 2).aestronglyMeasurable
      · filter_upwards with ω
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        nlinarith [(cayleyCutoff_pos N (ω : ℂ)).le, cayleyCutoff_le_one N (ω : ℂ)]
    refine hψint.congr ?_
    filter_upwards with ω
    have hc : ‖(ω : ℂ)‖ = 1 := by
      have hmem := cayley_spectrum_subset_circle U hgrp hU0 hUinner hUbd hSC ω.2
      rwa [mem_sphere_zero_iff_norm] at hmem
    rw [cayleyExpBump_sub_norm t N hc]
  -- the L² norms tend to 0
  have hL2 := cayleyExpBump_L2_tendsto_zero U hgrp hU0 hUinner hUbd hSC t x
  rw [Metric.tendsto_atTop] at hL2
  -- assemble the L²-Cauchy condition and invoke the existence half
  refine cayley_cfc_cauchySeq_of_integral U hgrp hU0 hUinner hUbd hSC
    (fun N z => cayleyExpBump t N z) (fun N => cayleyExpBump_continuousOn U hgrp hU0 hUinner hUbd hSC t N) x ?_
  intro ε hε
  obtain ⟨N, hN⟩ := hL2 (ε / 4) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have key : ∀ k, N ≤ k → ∫ ω, ‖cayleyExp t (ω : ℂ) * (cayleyBump k (ω : ℂ) : ℂ) - cayleyExp t (ω : ℂ)‖ ^ 2
      ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) < ε / 4 := by
    intro k hk
    have hd := hN k hk
    have hnn : 0 ≤ ∫ ω, ‖cayleyExp t (ω : ℂ) * (cayleyBump k (ω : ℂ) : ℂ) - cayleyExp t (ω : ℂ)‖ ^ 2
        ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) :=
      integral_nonneg (fun ω => sq_nonneg _)
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at hd
  show ∫ ω, ‖cayleyExpBump t m (ω : ℂ) - cayleyExpBump t n (ω : ℂ)‖ ^ 2
      ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) < ε
  calc ∫ ω, ‖cayleyExpBump t m (ω : ℂ) - cayleyExpBump t n (ω : ℂ)‖ ^ 2
        ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x)
      ≤ ∫ ω, (2 * ‖cayleyExp t (ω : ℂ) * (cayleyBump m (ω : ℂ) : ℂ) - cayleyExp t (ω : ℂ)‖ ^ 2
          + 2 * ‖cayleyExp t (ω : ℂ) * (cayleyBump n (ω : ℂ) : ℂ) - cayleyExp t (ω : ℂ)‖ ^ 2)
        ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun ω => sq_nonneg _)
        · exact ((hint m).const_mul 2).add ((hint n).const_mul 2)
        refine Filter.Eventually.of_forall (fun ω => ?_)
        simp only [cayleyExpBump]
        set c := cayleyExp t (ω : ℂ) with hcdef
        set a := c * (cayleyBump m (ω : ℂ) : ℂ) with ha
        set b := c * (cayleyBump n (ω : ℂ) : ℂ) with hb
        have h1 : ‖a - b‖ ≤ ‖a - c‖ + ‖b - c‖ := by
          have he : a - b = (a - c) - (b - c) := by ring
          rw [he]; exact norm_sub_le _ _
        nlinarith [h1, norm_nonneg (a - b), norm_nonneg (a - c), norm_nonneg (b - c),
          sq_nonneg (‖a - c‖ - ‖b - c‖)]
    _ = 2 * (∫ ω, ‖cayleyExp t (ω : ℂ) * (cayleyBump m (ω : ℂ) : ℂ) - cayleyExp t (ω : ℂ)‖ ^ 2
          ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))
        + 2 * (∫ ω, ‖cayleyExp t (ω : ℂ) * (cayleyBump n (ω : ℂ) : ℂ) - cayleyExp t (ω : ℂ)‖ ^ 2
          ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x)) := by
        rw [integral_add ((hint m).const_mul 2) ((hint n).const_mul 2), integral_const_mul, integral_const_mul]
    _ < ε := by have hbm := key m hm; have hbn := key n hn; linarith

/-- **★★★ The continuum Stone exponential `U_t x = exp(it A) x`** — defined as the strong limit of the cutoff
    functional-calculus vectors `U_t x := lim_N cfc(g_{t,N}) V x` (which exists by `cayleyExpBump_cfc_cauchySeq` and
    completeness of `H`).  This is `cfc(e_t) V x` for the (bounded Borel, `μ_x`-a.e. continuous) Stone-exponential
    symbol `e_t(ω) = exp(it · invCayley(ω))`, the genuine continuum unitary group of the self-adjoint generator
    `A = i(1 + V)(1 − V)⁻¹` — built with NO projection-valued measure.  Axiom-free; free scalar; no UV datum. -/
noncomputable def cayleyStoneU [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y))
    (t : ℝ) (x : H) : H :=
  (cauchySeq_tendsto_of_complete (cayleyExpBump_cfc_cauchySeq U hgrp hU0 hUinner hUbd hSC t x)).choose

/-- **The defining property of `U_t`:** `cfc(g_{t,N}) V x → U_t x` strongly (`U_t` is the strong limit). -/
theorem cayleyStoneU_tendsto [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (t : ℝ) (x : H) :
    Filter.Tendsto (fun N => cfc (cayleyExpBump t N)
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x)
      Filter.atTop (nhds (cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x)) :=
  (cauchySeq_tendsto_of_complete (cayleyExpBump_cfc_cauchySeq U hgrp hU0 hUinner hUbd hSC t x)).choose_spec

/-- **`U_t` is additive:** `U_t(x + y) = U_t x + U_t y`.  Each `cfc(g_{t,N}) V` is a (linear) bounded operator, so
    `cfc(g_{t,N}) V (x+y) = cfc(g_{t,N}) V x + cfc(g_{t,N}) V y`; pass to the strong limit (`Tendsto.add` + uniqueness).
    With `cayleyStoneU_smul`, `U_t` is a ℂ-linear operator (toward `U_t ∈ unitary(H)`). -/
theorem cayleyStoneU_add [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (t : ℝ) (x y : H) :
    cayleyStoneU U hgrp hU0 hUinner hUbd hSC t (x + y)
      = cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x + cayleyStoneU U hgrp hU0 hUinner hUbd hSC t y := by
  have hxy := cayleyStoneU_tendsto U hgrp hU0 hUinner hUbd hSC t (x + y)
  have hsum := (cayleyStoneU_tendsto U hgrp hU0 hUinner hUbd hSC t x).add
    (cayleyStoneU_tendsto U hgrp hU0 hUinner hUbd hSC t y)
  have heq : (fun N => cfc (cayleyExpBump t N)
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) (x + y))
      = (fun N => cfc (cayleyExpBump t N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x
          + cfc (cayleyExpBump t N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) y) := by
    funext N; rw [map_add]
  rw [heq] at hxy
  exact tendsto_nhds_unique hxy hsum

/-- **`U_t` is ℂ-homogeneous:** `U_t(c • x) = c • U_t x`.  As `cayleyStoneU_add`, from the linearity of each
    `cfc(g_{t,N}) V` (`map_smul`) and `Tendsto.const_smul` + uniqueness. -/
theorem cayleyStoneU_smul [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y))
    (t : ℝ) (c : ℂ) (x : H) :
    cayleyStoneU U hgrp hU0 hUinner hUbd hSC t (c • x)
      = c • cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x := by
  have hcx := cayleyStoneU_tendsto U hgrp hU0 hUinner hUbd hSC t (c • x)
  have hsm := (cayleyStoneU_tendsto U hgrp hU0 hUinner hUbd hSC t x).const_smul c
  have heq : (fun N => cfc (cayleyExpBump t N)
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) (c • x))
      = (fun N => c • cfc (cayleyExpBump t N)
          (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x) := by
    funext N; rw [map_smul]
  rw [heq] at hcx
  exact tendsto_nhds_unique hcx hsm

/-- **`U_0 = id`** — the identity element of the Stone group.  At `t = 0` the symbol is `e_0 ≡ 1`
    (`cayleyExp_zero`), so the cutoff symbol is `g_{0,N} = e_0 · η_N = η_N = 1 − ψ_N`, hence
    `cfc(g_{0,N}) V x = x − cfc(ψ_N) V x`.  The atom-killing limit `cfc(ψ_N) V x → 0`
    (`cayleyCutoff_cfc_tendsto_zero`, valid because `μ_x({1}) = 0`) then gives `x − 0 = x`, and by
    uniqueness of strong limits `U_0 x = x`.  The first of the three remaining unitary-group bricks
    (`U_0 = 1`, isometry `‖U_t x‖ = ‖x‖`, group law `U_s U_t = U_{s+t}`). -/
theorem cayleyStoneU_zero [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H) :
    cayleyStoneU U hgrp hU0 hUinner hUbd hSC 0 x = x := by
  -- the defining strong limit at `t = 0`
  have htends := cayleyStoneU_tendsto U hgrp hU0 hUinner hUbd hSC 0 x
  -- at `t = 0` the cutoff symbol is `g_{0,N} = η_N = 1 − ψ_N`, so `cfc(g_{0,N}) V x = x − cfc(ψ_N) V x`
  have hrw : (fun N => cfc (cayleyExpBump 0 N)
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x)
      = (fun N => x - cfc (fun z => (cayleyCutoff N z : ℂ))
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x) := by
    funext N
    have hsymb : cayleyExpBump 0 N
        = (fun z => (1 : ℂ → ℂ) z - (fun w => (cayleyCutoff N w : ℂ)) z) := by
      funext ω
      simp only [cayleyExpBump, cayleyExp_zero, cayleyBump, one_mul, Pi.one_apply]
      push_cast
      ring
    rw [hsymb, cfc_sub (f := (1 : ℂ → ℂ)) (g := fun w => (cayleyCutoff N w : ℂ))
        (a := (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H))
        (hg := (Complex.continuous_ofReal.comp (cayleyCutoff_continuous N)).continuousOn),
      cayley_cfc_one U hgrp hU0 hUinner hUbd hSC]
    simp [ContinuousLinearMap.sub_apply]
  rw [hrw] at htends
  -- `x − cfc(ψ_N) V x → x − 0 = x`
  have hlim : Filter.Tendsto (fun N => x - cfc (fun z => (cayleyCutoff N z : ℂ))
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x) Filter.atTop (nhds x) := by
    have h0 : nhds x = nhds (x - 0) := by rw [sub_zero]
    rw [h0]
    exact tendsto_const_nhds.sub (cayleyCutoff_cfc_tendsto_zero U hgrp hU0 hUinner hUbd hSC x)
  exact tendsto_nhds_unique htends hlim

/-- **`∫ η_N² dμ_x → ‖x‖²`** — the `L²`-mass of the cutoff bump fills out the whole spectral measure.  Expand
    `η_N² = (1 − ψ_N)² = 1 − 2ψ_N + ψ_N²`; integrate termwise (all integrands bounded on the finite measure `μ_x`):
    `∫ η_N² dμ_x = μ_x(σ(V)).toReal − 2 ∫ ψ_N dμ_x + ∫ ψ_N² dμ_x`.  The total mass is `μ_x(σ(V)).toReal = ‖x‖²`
    (`cayleyScalarMeasure_univ`), and both cutoff integrals vanish: `∫ ψ_N → μ_x({1}) = 0`
    (`cayleyCutoff_integral_tendsto_atom` + `cayleyScalarMeasure_atom_eq_zero`) and `∫ ψ_N² → 0`
    (`cayleyCutoff_sq_integral_tendsto_zero`).  Hence `∫ η_N² → ‖x‖² − 0 + 0 = ‖x‖²` — the limiting `L²`-norm of the
    cutoff symbol equals the total Born mass, the source of the `U_t` isometry. -/
theorem cayleyBump_sq_integral_tendsto [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H) :
    Filter.Tendsto
      (fun N => ∫ ω, (cayleyBump N (ω : ℂ)) ^ 2 ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))
      Filter.atTop (nhds (‖x‖ ^ 2)) := by
  haveI : IsFiniteMeasure (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) :=
    cayleyScalarMeasure_isFiniteMeasure U hgrp hU0 hUinner hUbd hSC x
  have hIψ : ∀ N, Integrable
      (fun ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) => cayleyCutoff N (ω : ℂ))
      (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := by
    intro N
    refine (integrable_const (1 : ℝ)).mono' ?_ ?_
    · exact ((cayleyCutoff_continuous N).comp continuous_subtype_val).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_of_nonneg (cayleyCutoff_pos N _).le]; exact cayleyCutoff_le_one N _
  have hIψ2 : ∀ N, Integrable
      (fun ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) =>
        (cayleyCutoff N (ω : ℂ)) ^ 2)
      (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := by
    intro N
    refine (integrable_const (1 : ℝ)).mono' ?_ ?_
    · exact (((cayleyCutoff_continuous N).comp continuous_subtype_val).pow 2).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      nlinarith [(cayleyCutoff_pos N (ω : ℂ)).le, cayleyCutoff_le_one N (ω : ℂ)]
  -- `∫ η_N² = ‖x‖² − 2 ∫ ψ_N + ∫ ψ_N²` (expand the square, integrate termwise, total mass `= ‖x‖²`)
  have hexp : ∀ N, (∫ ω, (cayleyBump N (ω : ℂ)) ^ 2 ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))
      = ‖x‖ ^ 2 - 2 * (∫ ω, cayleyCutoff N (ω : ℂ) ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))
        + (∫ ω, (cayleyCutoff N (ω : ℂ)) ^ 2 ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x)) := by
    intro N
    have hpt : (fun ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) =>
        (cayleyBump N (ω : ℂ)) ^ 2)
        = (fun ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) =>
            ((1 : ℝ) - 2 * cayleyCutoff N (ω : ℂ)) + (cayleyCutoff N (ω : ℂ)) ^ 2) := by
      funext ω; simp only [cayleyBump]; ring
    -- split the integral termwise (`have`-with-explicit-type forces defeq elaboration of `integral_add`/`_sub`)
    have e1 : (∫ ω, ((1 : ℝ) - 2 * cayleyCutoff N (ω : ℂ)) + (cayleyCutoff N (ω : ℂ)) ^ 2
          ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))
        = (∫ ω, ((1 : ℝ) - 2 * cayleyCutoff N (ω : ℂ))
            ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))
          + ∫ ω, (cayleyCutoff N (ω : ℂ)) ^ 2 ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) :=
      integral_add ((integrable_const (1 : ℝ)).sub ((hIψ N).const_mul 2)) (hIψ2 N)
    have e2 : (∫ ω, ((1 : ℝ) - 2 * cayleyCutoff N (ω : ℂ))
          ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))
        = (∫ ω, (1 : ℝ) ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))
          - ∫ ω, 2 * cayleyCutoff N (ω : ℂ) ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) :=
      integral_sub (integrable_const (1 : ℝ)) ((hIψ N).const_mul 2)
    have e3 : (∫ ω, 2 * cayleyCutoff N (ω : ℂ) ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))
        = 2 * ∫ ω, cayleyCutoff N (ω : ℂ) ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) :=
      integral_const_mul 2 _
    have e4 : (∫ ω, (1 : ℝ) ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x)) = ‖x‖ ^ 2 := by
      rw [integral_const, smul_eq_mul, mul_one]
      exact cayleyScalarMeasure_univ U hgrp hU0 hUinner hUbd hSC x
    rw [hpt, e1, e2, e3, e4]
  -- `∫ ψ_N → μ_x({1}) = 0` and `∫ ψ_N² → 0`
  have hatom : Filter.Tendsto
      (fun N => ∫ ω, cayleyCutoff N (ω : ℂ) ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))
      Filter.atTop (nhds 0) := by
    have h := cayleyCutoff_integral_tendsto_atom U hgrp hU0 hUinner hUbd hSC x
    rwa [cayleyScalarMeasure_atom_eq_zero U hgrp hU0 hUinner hUbd hSC x, ENNReal.toReal_zero] at h
  have hsq := cayleyCutoff_sq_integral_tendsto_zero U hgrp hU0 hUinner hUbd hSC x
  simp only [hexp]
  have key : Filter.Tendsto
      (fun N => ‖x‖ ^ 2 - 2 * (∫ ω, cayleyCutoff N (ω : ℂ)
          ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))
        + (∫ ω, (cayleyCutoff N (ω : ℂ)) ^ 2 ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x)))
      Filter.atTop (nhds (‖x‖ ^ 2 - 2 * 0 + 0)) :=
    (tendsto_const_nhds.sub (hatom.const_mul 2)).add hsq
  simpa using key

/-- **`‖U_t x‖ = ‖x‖` — the Stone exponential is an isometry** (toward `U_t ∈ unitary(H)`).  By Parseval
    (`cayley_cfc_norm_sq_integral`) the cutoff vectors have squared norm `‖cfc(g_{t,N}) V x‖² = ∫ ‖g_{t,N}‖² dμ_x`,
    and on `σ(V) ⊆ S¹` the symbol has modulus `‖g_{t,N}(ω)‖ = η_N(ω)` (`cayleyExpBump_norm`, since `‖e_t‖ = 1`), so
    `‖cfc(g_{t,N}) V x‖² = ∫ η_N² dμ_x → ‖x‖²` (`cayleyBump_sq_integral_tendsto`).  The same sequence also tends to
    `‖U_t x‖²` (norm is continuous along the defining strong limit `cayleyStoneU_tendsto`), so by uniqueness
    `‖U_t x‖² = ‖x‖²`, hence `‖U_t x‖ = ‖x‖` (both nonnegative, `Real.sqrt_sq`).  The second of the three remaining
    unitary-group bricks.  Axiom-free; free scalar; no UV datum. -/
theorem cayleyStoneU_isometry [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (t : ℝ) (x : H) :
    ‖cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x‖ = ‖x‖ := by
  -- `‖cfc(g_{t,N}) V x‖² = ∫ η_N² dμ_x` (Parseval + `‖g_{t,N}‖ = η_N` on the circle)
  have hnormsq : ∀ N, ‖cfc (cayleyExpBump t N)
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x‖ ^ 2
      = ∫ ω, (cayleyBump N (ω : ℂ)) ^ 2 ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := by
    intro N
    rw [cayley_cfc_norm_sq_integral U hgrp hU0 hUinner hUbd hSC (cayleyExpBump t N)
      (cayleyExpBump_continuousOn U hgrp hU0 hUinner hUbd hSC t N) x]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
    have hcirc : ‖(ω : ℂ)‖ = 1 := by
      have hmem := cayley_spectrum_subset_circle U hgrp hU0 hUinner hUbd hSC ω.2
      rwa [mem_sphere_zero_iff_norm] at hmem
    show ‖cayleyExpBump t N (ω : ℂ)‖ ^ 2 = (cayleyBump N (ω : ℂ)) ^ 2
    rw [cayleyExpBump_norm t N hcirc]
  -- the squared-norm sequence tends to `‖x‖²` …
  have hsqlim : Filter.Tendsto (fun N => ‖cfc (cayleyExpBump t N)
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x‖ ^ 2)
      Filter.atTop (nhds (‖x‖ ^ 2)) := by
    simp only [hnormsq]
    exact cayleyBump_sq_integral_tendsto U hgrp hU0 hUinner hUbd hSC x
  -- … and also to `‖U_t x‖²` (norm continuous along the defining strong limit)
  have hsqlim2 : Filter.Tendsto (fun N => ‖cfc (cayleyExpBump t N)
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x‖ ^ 2)
      Filter.atTop (nhds (‖cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x‖ ^ 2)) :=
    ((cayleyStoneU_tendsto U hgrp hU0 hUinner hUbd hSC t x).norm).pow 2
  -- uniqueness of limits ⟹ `‖U_t x‖² = ‖x‖²`, then take square roots (both nonnegative)
  have h2 : ‖cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x‖ ^ 2 = ‖x‖ ^ 2 :=
    tendsto_nhds_unique hsqlim2 hsqlim
  calc ‖cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x‖
      = Real.sqrt (‖cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖x‖ ^ 2) := by rw [h2]
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)

/-- **`U_t` bundled as a ℂ-linear isometry** `H →ₗᵢ[ℂ] H`.  The strong-limit map `cayleyStoneU` is additive
    (`cayleyStoneU_add`), ℂ-homogeneous (`cayleyStoneU_smul`) and norm-preserving (`cayleyStoneU_isometry`), so it
    assembles into a genuine `LinearIsometry`.  (Surjectivity — hence `U_t ∈ unitary(H)` — needs the group law
    `U_{-t} U_t = 1`, a later brick; an isometry is already injective with closed range.) -/
noncomputable def cayleyStoneLI [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (t : ℝ) :
    H →ₗᵢ[ℂ] H where
  toFun := cayleyStoneU U hgrp hU0 hUinner hUbd hSC t
  map_add' := cayleyStoneU_add U hgrp hU0 hUinner hUbd hSC t
  map_smul' := cayleyStoneU_smul U hgrp hU0 hUinner hUbd hSC t
  norm_map' := cayleyStoneU_isometry U hgrp hU0 hUinner hUbd hSC t

/-- **`U_t` bundled as a bounded operator** `H →L[ℂ] H` (the continuous linear map underlying the isometry
    `cayleyStoneLI`).  This is the packaging Stone's theorem consumes: the one-parameter group `t ↦ U_t` lives in
    `H →L[ℂ] H`, where the group law `U_s U_t = U_{s+t}` reads as operator composition and the generator is read off
    by differentiation. -/
noncomputable def cayleyStoneCLM [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (t : ℝ) :
    H →L[ℂ] H :=
  (cayleyStoneLI U hgrp hU0 hUinner hUbd hSC t).toContinuousLinearMap

/-- The bundled operator acts as the strong-limit map: `cayleyStoneCLM U … t x = cayleyStoneU U … t x`. -/
@[simp] theorem cayleyStoneCLM_apply [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (t : ℝ) (x : H) :
    cayleyStoneCLM U hgrp hU0 hUinner hUbd hSC t x = cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x := rfl

/-- The bundled operator is an isometry: `‖cayleyStoneCLM U … t x‖ = ‖x‖` (restating `cayleyStoneU_isometry`
    at the `H →L[ℂ] H` level). -/
theorem cayleyStoneCLM_norm_map [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (t : ℝ) (x : H) :
    ‖cayleyStoneCLM U hgrp hU0 hUinner hUbd hSC t x‖ = ‖x‖ :=
  cayleyStoneU_isometry U hgrp hU0 hUinner hUbd hSC t x

/-- **The cutoff cfc operators are contractions:** `‖cfc(g_{t,N}) V z‖ ≤ ‖z‖`.  By Parseval the squared norm is
    `∫ ‖g_{t,N}‖² dμ_z`, and on `σ(V) ⊆ S¹` the symbol has modulus `‖g_{t,N}(ω)‖ = η_N(ω) ≤ 1`
    (`cayleyExpBump_norm`, `cayleyBump_le_one`), so `∫ ‖g_{t,N}‖² dμ_z ≤ ∫ 1 dμ_z = ‖z‖²`.  This uniform operator
    bound (`‖cfc(g_{t,N}) V‖ ≤ 1` for every `N`) is what the operator-limit step of the group law `U_s U_t = U_{s+t}`
    consumes: a uniformly bounded net of operators converging strongly composes with a convergent vector net. -/
theorem cayleyExpBump_cfc_norm_le [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y))
    (t : ℝ) (N : ℕ) (z : H) :
    ‖cfc (cayleyExpBump t N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z‖ ≤ ‖z‖ := by
  haveI : IsFiniteMeasure (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC z) :=
    cayleyScalarMeasure_isFiniteMeasure U hgrp hU0 hUinner hUbd hSC z
  have hsq : ‖cfc (cayleyExpBump t N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z‖ ^ 2
      ≤ ‖z‖ ^ 2 := by
    rw [cayley_cfc_norm_sq_integral U hgrp hU0 hUinner hUbd hSC (cayleyExpBump t N)
      (cayleyExpBump_continuousOn U hgrp hU0 hUinner hUbd hSC t N) z]
    have hle : (∫ ω, ‖cayleyExpBump t N (ω : ℂ)‖ ^ 2
          ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC z))
        ≤ ∫ ω, (1 : ℝ) ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC z) := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun ω => sq_nonneg _)
      · exact integrable_const 1
      · filter_upwards with ω
        have hcirc : ‖(ω : ℂ)‖ = 1 := by
          have hmem := cayley_spectrum_subset_circle U hgrp hU0 hUinner hUbd hSC ω.2
          rwa [mem_sphere_zero_iff_norm] at hmem
        rw [cayleyExpBump_norm t N hcirc]
        nlinarith [cayleyBump_nonneg N (ω : ℂ), cayleyBump_le_one N (ω : ℂ)]
    have he4 : (∫ ω, (1 : ℝ) ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC z)) = ‖z‖ ^ 2 := by
      rw [integral_const, smul_eq_mul, mul_one]
      exact cayleyScalarMeasure_univ U hgrp hU0 hUinner hUbd hSC z
    exact hle.trans_eq he4
  calc ‖cfc (cayleyExpBump t N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z‖
      = Real.sqrt (‖cfc (cayleyExpBump t N)
          (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖z‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖z‖ := Real.sqrt_sq (norm_nonneg _)

/-- **cfc multiplicativity for the cutoff operators:** `cfc(g_{s,N}) V (cfc(g_{t,N}) V x) = cfc(e_{s+t}·η_N²) V x`.
    Since both cutoff symbols are continuous on `σ(V)` (`cayleyExpBump_continuousOn`), the continuous functional
    calculus is multiplicative: `cfc(g_{s,N}) V ∘ cfc(g_{t,N}) V = cfc(g_{s,N}·g_{t,N}) V`, and the product symbol
    is `g_{s,N}·g_{t,N} = (e_s η_N)(e_t η_N) = e_s e_t η_N² = e_{s+t} η_N²` (`cayleyExp_add`).  This is the algebraic
    half of the group law `U_s U_t = U_{s+t}`: passing `N → ∞` on the right (`e_{s+t} η_N² → e_{s+t}` in `L²`) and on
    the left (operator-limit of the contractions `cayleyExpBump_cfc_norm_le`) yields the group law. -/
theorem cayleyExpBump_cfc_comp [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y))
    (s t : ℝ) (N : ℕ) (x : H) :
    cfc (cayleyExpBump s N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
        (cfc (cayleyExpBump t N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x)
      = cfc (fun ω => cayleyExp (s + t) ω * ((cayleyBump N ω : ℂ)) ^ 2)
          (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x := by
  have hsymb : (fun ω : ℂ => cayleyExpBump s N ω * cayleyExpBump t N ω)
      = (fun ω : ℂ => cayleyExp (s + t) ω * ((cayleyBump N ω : ℂ)) ^ 2) := by
    funext ω
    simp only [cayleyExpBump]
    have hr : cayleyExp s ω * (cayleyBump N ω : ℂ) * (cayleyExp t ω * (cayleyBump N ω : ℂ))
        = (cayleyExp s ω * cayleyExp t ω) * ((cayleyBump N ω : ℂ)) ^ 2 := by ring
    rw [hr, cayleyExp_add]
  rw [← ContinuousLinearMap.mul_apply,
    ← cfc_mul (cayleyExpBump s N) (cayleyExpBump t N)
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
      (cayleyExpBump_continuousOn U hgrp hU0 hUinner hUbd hSC s N)
      (cayleyExpBump_continuousOn U hgrp hU0 hUinner hUbd hSC t N),
    hsymb]

/-- **The squared cutoff symbol converges to the same Stone limit:** `cfc(e_r·η_N²) V x → U_r x`.  The squared
    bump `e_r η_N²` differs from the single bump `g_{r,N} = e_r η_N` by `e_r η_N(η_N − 1) = −e_r η_N ψ_N`, whose
    `L²(μ_x)`-norm² is `∫ η_N² ψ_N² dμ_x ≤ ∫ ψ_N² dμ_x → 0` (`cayley_cfc_sub_norm_sq_integral` +
    `cayleyCutoff_sq_integral_tendsto_zero`).  So `cfc(e_r η_N²) V x` and `cfc(g_{r,N}) V x` share the limit, and the
    latter is `U_r x` by `cayleyStoneU_tendsto`.  This is the right-hand `N → ∞` half of the group law:
    `cayleyExpBump_cfc_comp` writes `U_s U_t` as the limit of `cfc(e_{s+t} η_N²) V x`, which this lemma identifies
    with `U_{s+t} x`. -/
theorem cayleyProdSymbol_cfc_tendsto [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (r : ℝ) (x : H) :
    Filter.Tendsto (fun N => cfc (fun ω => cayleyExp r ω * ((cayleyBump N ω : ℂ)) ^ 2)
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x)
      Filter.atTop (nhds (cayleyStoneU U hgrp hU0 hUinner hUbd hSC r x)) := by
  haveI : IsFiniteMeasure (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) :=
    cayleyScalarMeasure_isFiniteMeasure U hgrp hU0 hUinner hUbd hSC x
  -- the squared symbol is continuous on σ(V): `e_r η_N² = g_{r,N} · η_N`
  have hcont : ∀ N, ContinuousOn (fun ω => cayleyExp r ω * ((cayleyBump N ω : ℂ)) ^ 2)
      (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) := by
    intro N
    have heq : (fun ω => cayleyExp r ω * ((cayleyBump N ω : ℂ)) ^ 2)
        = (fun ω => cayleyExpBump r N ω * (cayleyBump N ω : ℂ)) := by
      funext ω; simp only [cayleyExpBump]; ring
    rw [heq]
    exact (cayleyExpBump_continuousOn U hgrp hU0 hUinner hUbd hSC r N).mul
      ((Complex.continuous_ofReal.comp (cayleyBump_continuous N)).continuousOn)
  -- the single-bump vectors converge to U_r x
  have hg := cayleyStoneU_tendsto U hgrp hU0 hUinner hUbd hSC r x
  -- the difference `cfc(g_{r,N}) - cfc(e_r η_N²)` → 0 in L² hence strongly
  have hdiff : Filter.Tendsto (fun N => cfc (cayleyExpBump r N)
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x
      - cfc (fun ω => cayleyExp r ω * ((cayleyBump N ω : ℂ)) ^ 2)
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hψsq := cayleyCutoff_sq_integral_tendsto_zero U hgrp hU0 hUinner hUbd hSC x
    have hsqrt : Filter.Tendsto (fun N => Real.sqrt
        (∫ ω, (cayleyCutoff N (ω : ℂ)) ^ 2 ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x)))
        Filter.atTop (nhds 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hψsq
      rwa [Real.sqrt_zero] at h
    refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hsqrt
    have hb : ‖cfc (cayleyExpBump r N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x
          - cfc (fun ω => cayleyExp r ω * ((cayleyBump N ω : ℂ)) ^ 2)
            (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x‖ ^ 2
        ≤ ∫ ω, (cayleyCutoff N (ω : ℂ)) ^ 2 ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := by
      rw [cayley_cfc_sub_norm_sq_integral U hgrp hU0 hUinner hUbd hSC (cayleyExpBump r N)
        (fun ω => cayleyExp r ω * ((cayleyBump N ω : ℂ)) ^ 2)
        (cayleyExpBump_continuousOn U hgrp hU0 hUinner hUbd hSC r N) (hcont N) x]
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
      · refine (integrable_const (1 : ℝ)).mono' ?_ ?_
        · exact (((cayleyCutoff_continuous N).comp continuous_subtype_val).pow 2).aestronglyMeasurable
        · filter_upwards with ω
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          nlinarith [(cayleyCutoff_pos N (ω : ℂ)).le, cayleyCutoff_le_one N (ω : ℂ)]
      · filter_upwards with ω
        have hcirc : ‖(ω : ℂ)‖ = 1 := by
          have hmem := cayley_spectrum_subset_circle U hgrp hU0 hUinner hUbd hSC ω.2
          rwa [mem_sphere_zero_iff_norm] at hmem
        have hfac : cayleyExpBump r N (ω : ℂ) - cayleyExp r (ω : ℂ) * ((cayleyBump N (ω : ℂ) : ℂ)) ^ 2
            = cayleyExp r (ω : ℂ) * ((cayleyBump N (ω : ℂ) : ℂ)) * ((cayleyCutoff N (ω : ℂ) : ℂ)) := by
          simp only [cayleyExpBump, cayleyBump]; push_cast; ring
        rw [hfac, norm_mul, norm_mul, cayleyExp_abs_circle hcirc, one_mul, Complex.norm_real,
          Complex.norm_real, Real.norm_of_nonneg (cayleyBump_nonneg N _),
          Real.norm_of_nonneg (cayleyCutoff_pos N _).le]
        have hη2 : cayleyBump N (ω : ℂ) ^ 2 ≤ 1 := by
          nlinarith [cayleyBump_nonneg N (ω : ℂ), cayleyBump_le_one N (ω : ℂ)]
        nlinarith [mul_nonneg (sub_nonneg.mpr hη2) (sq_nonneg (cayleyCutoff N (ω : ℂ)))]
    calc ‖cfc (cayleyExpBump r N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x
            - cfc (fun ω => cayleyExp r ω * ((cayleyBump N ω : ℂ)) ^ 2)
              (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x‖
        = Real.sqrt (‖cfc (cayleyExpBump r N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x
            - cfc (fun ω => cayleyExp r ω * ((cayleyBump N ω : ℂ)) ^ 2)
              (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (∫ ω, (cayleyCutoff N (ω : ℂ)) ^ 2
            ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x)) := Real.sqrt_le_sqrt hb
  -- `cfc(e_r η_N²) V x = cfc(g_{r,N}) V x − (difference) → U_r x − 0`
  have hcomb := hg.sub hdiff
  simpa using hcomb

/-- **★★★★★ THE ONE-PARAMETER GROUP LAW** `U_s U_t = U_{s+t}` for the continuum Stone exponential.  With
    `A_N := cfc(g_{s,N}) V`, `y_N := cfc(g_{t,N}) V x` and `y := U_t x`, the composite `A_N y_N` converges two ways:
    **(i)** to `U_s (U_t x)` — splitting `A_N y_N − U_s(U_t x) = A_N(y_N − y) + (A_N y − U_s y)`, the first summand
    `→ 0` because `A_N` is a contraction (`cayleyExpBump_cfc_norm_le`) and `y_N → y` (`cayleyStoneU_tendsto`), the
    second by `cayleyStoneU_tendsto` at the fixed vector `y`; and **(ii)** to `U_{s+t} x` — because
    `A_N y_N = cfc(e_{s+t} η_N²) V x` (`cayleyExpBump_cfc_comp`) and that tends to `U_{s+t} x`
    (`cayleyProdSymbol_cfc_tendsto`).  Uniqueness of limits gives `U_s (U_t x) = U_{s+t} x`.  This is the missing
    multiplicative structure: `t ↦ U_t` is now a genuine one-parameter group of isometries.  Axiom-free; free scalar;
    no UV datum. -/
theorem cayleyStoneU_group [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (s t : ℝ) (x : H) :
    cayleyStoneU U hgrp hU0 hUinner hUbd hSC s (cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x)
      = cayleyStoneU U hgrp hU0 hUinner hUbd hSC (s + t) x := by
  -- (i) the operator-limit `A_N y_N → U_s (U_t x)`
  have hy := cayleyStoneU_tendsto U hgrp hU0 hUinner hUbd hSC t x
  have hAy := cayleyStoneU_tendsto U hgrp hU0 hUinner hUbd hSC s
    (cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x)
  have hynorm : Filter.Tendsto (fun N => ‖cfc (cayleyExpBump t N)
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x
      - cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x‖) Filter.atTop (nhds 0) := by
    have h := (hy.sub (tendsto_const_nhds (x := cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x))).norm
    simpa using h
  have hT1 : Filter.Tendsto (fun N => cfc (cayleyExpBump s N)
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
      (cfc (cayleyExpBump t N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x
        - cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x)) Filter.atTop (nhds 0) :=
    squeeze_zero_norm (fun N => cayleyExpBump_cfc_norm_le U hgrp hU0 hUinner hUbd hSC s N _) hynorm
  have hT2 : Filter.Tendsto (fun N => cfc (cayleyExpBump s N)
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
      (cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x)
      - cayleyStoneU U hgrp hU0 hUinner hUbd hSC s (cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x))
      Filter.atTop (nhds 0) := by
    have h := hAy.sub (tendsto_const_nhds
      (x := cayleyStoneU U hgrp hU0 hUinner hUbd hSC s (cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x)))
    simpa using h
  have hstep1 : Filter.Tendsto (fun N => cfc (cayleyExpBump s N)
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
      (cfc (cayleyExpBump t N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x))
      Filter.atTop (nhds (cayleyStoneU U hgrp hU0 hUinner hUbd hSC s
        (cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x))) := by
    have hcombine : (fun N => cfc (cayleyExpBump s N)
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
        (cfc (cayleyExpBump t N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x))
        = (fun N => (cfc (cayleyExpBump s N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
              (cfc (cayleyExpBump t N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x
                - cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x))
            + (cfc (cayleyExpBump s N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
                (cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x)
              - cayleyStoneU U hgrp hU0 hUinner hUbd hSC s (cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x))
            + cayleyStoneU U hgrp hU0 hUinner hUbd hSC s
                (cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x)) := by
      funext N; rw [map_sub]; abel
    rw [hcombine]
    simpa using (hT1.add hT2).add (tendsto_const_nhds
      (x := cayleyStoneU U hgrp hU0 hUinner hUbd hSC s (cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x)))
  -- (ii) the same composite equals `cfc(e_{s+t} η_N²) V x → U_{s+t} x`
  have hstep2 : Filter.Tendsto (fun N => cfc (cayleyExpBump s N)
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
      (cfc (cayleyExpBump t N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x))
      Filter.atTop (nhds (cayleyStoneU U hgrp hU0 hUinner hUbd hSC (s + t) x)) := by
    have hcomp : (fun N => cfc (cayleyExpBump s N)
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
        (cfc (cayleyExpBump t N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x))
        = (fun N => cfc (fun ω => cayleyExp (s + t) ω * ((cayleyBump N ω : ℂ)) ^ 2)
            (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x) := by
      funext N; exact cayleyExpBump_cfc_comp U hgrp hU0 hUinner hUbd hSC s t N x
    rw [hcomp]
    exact cayleyProdSymbol_cfc_tendsto U hgrp hU0 hUinner hUbd hSC (s + t) x
  exact tendsto_nhds_unique hstep1 hstep2

/-- **`U_{-t}` is a left inverse of `U_t`:** `U_{-t}(U_t x) = x`.  Immediate from the group law
    (`cayleyStoneU_group` with `s = -t`) and the identity `U_0 = 1` (`cayleyStoneU_zero`), since `(-t) + t = 0`. -/
theorem cayleyStoneU_neg_left [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (t : ℝ) (x : H) :
    cayleyStoneU U hgrp hU0 hUinner hUbd hSC (-t)
      (cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x) = x := by
  rw [cayleyStoneU_group U hgrp hU0 hUinner hUbd hSC (-t) t x, neg_add_cancel]
  exact cayleyStoneU_zero U hgrp hU0 hUinner hUbd hSC x

/-- **`U_{-t}` is a right inverse of `U_t`:** `U_t(U_{-t} x) = x` (group law with `s = t`, `(-t)`; `t + (-t) = 0`). -/
theorem cayleyStoneU_neg_right [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (t : ℝ) (x : H) :
    cayleyStoneU U hgrp hU0 hUinner hUbd hSC t
      (cayleyStoneU U hgrp hU0 hUinner hUbd hSC (-t) x) = x := by
  rw [cayleyStoneU_group U hgrp hU0 hUinner hUbd hSC t (-t) x, add_neg_cancel]
  exact cayleyStoneU_zero U hgrp hU0 hUinner hUbd hSC x

/-- **`U_t` bundled as a unitary** `H ≃ₗᵢ[ℂ] H`.  The group law upgrades the linear isometry `cayleyStoneLI` to a
    surjective one: `U_{-t}` is a two-sided inverse (`cayleyStoneU_neg_left`/`cayleyStoneU_neg_right`), so `U_t` is a
    `LinearIsometryEquiv` — i.e. `U_t ∈ unitary(H)`.  The continuum Stone exponential is now a genuine one-parameter
    group of unitaries `t ↦ U_t = exp(it A)`, all axiom-free with no PVM and no UV datum; only strong continuity and
    the generator identification remain for the full Stone correspondence. -/
noncomputable def cayleyStoneLIE [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (t : ℝ) :
    H ≃ₗᵢ[ℂ] H where
  toFun := cayleyStoneU U hgrp hU0 hUinner hUbd hSC t
  map_add' := cayleyStoneU_add U hgrp hU0 hUinner hUbd hSC t
  map_smul' := cayleyStoneU_smul U hgrp hU0 hUinner hUbd hSC t
  invFun := cayleyStoneU U hgrp hU0 hUinner hUbd hSC (-t)
  left_inv := cayleyStoneU_neg_left U hgrp hU0 hUinner hUbd hSC t
  right_inv := cayleyStoneU_neg_right U hgrp hU0 hUinner hUbd hSC t
  norm_map' := cayleyStoneU_isometry U hgrp hU0 hUinner hUbd hSC t

/-- The bundled unitary acts as the strong-limit map: `cayleyStoneLIE U … t x = cayleyStoneU U … t x`. -/
@[simp] theorem cayleyStoneLIE_apply [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (t : ℝ) (x : H) :
    cayleyStoneLIE U hgrp hU0 hUinner hUbd hSC t x = cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x := rfl

/-- **The limit Parseval identity for the Stone group:** `‖U_t x − U_s x‖² = ∫ ‖e_t − e_s‖² dμ_x`, where
    `e_r(ω) = cayleyExp r ω = exp(it·c(ω))` is the (bounded Borel) Stone-exponential symbol.  This transports the
    `L²`-isometry through the strong limit: the cutoff differences satisfy `‖cfc(g_{t,N}) V x − cfc(g_{s,N}) V x‖² =
    ∫ ‖g_{t,N} − g_{s,N}‖² dμ_x` (`cayley_cfc_sub_norm_sq_integral`), the left side `→ ‖U_t x − U_s x‖²` (norm
    continuity along `cayleyStoneU_tendsto`), and the right side `→ ∫ ‖e_t − e_s‖² dμ_x` by dominated convergence
    (`g_{t,N} − g_{s,N} = η_N(e_t − e_s)`, `η_N² → 1` `μ_x`-a.e. since `μ_x({1}) = 0`, dominated by the constant `4`).
    Uniqueness of limits gives the identity — the bridge to strong continuity (`t ↦ U_t x`), since the RHS `→ 0` as
    `t → s` by a second dominated-convergence pass. -/
theorem cayleyStoneU_sub_norm_sq [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (s t : ℝ) (x : H) :
    ‖cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x - cayleyStoneU U hgrp hU0 hUinner hUbd hSC s x‖ ^ 2
      = ∫ ω, ‖cayleyExp t (ω : ℂ) - cayleyExp s (ω : ℂ)‖ ^ 2
        ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := by
  haveI : IsFiniteMeasure (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) :=
    cayleyScalarMeasure_isFiniteMeasure U hgrp hU0 hUinner hUbd hSC x
  -- (A) the cutoff-difference squared norm → ‖U_t x − U_s x‖²
  have hA : Filter.Tendsto (fun N => ‖cfc (cayleyExpBump t N)
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x
      - cfc (cayleyExpBump s N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x‖ ^ 2)
      Filter.atTop (nhds (‖cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x
        - cayleyStoneU U hgrp hU0 hUinner hUbd hSC s x‖ ^ 2)) :=
    (((cayleyStoneU_tendsto U hgrp hU0 hUinner hUbd hSC t x).sub
      (cayleyStoneU_tendsto U hgrp hU0 hUinner hUbd hSC s x)).norm).pow 2
  -- (B) and equals the L² integral of the symbol difference
  have hB : ∀ N, ‖cfc (cayleyExpBump t N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x
      - cfc (cayleyExpBump s N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) x‖ ^ 2
      = ∫ ω, ‖cayleyExpBump t N (ω : ℂ) - cayleyExpBump s N (ω : ℂ)‖ ^ 2
        ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) := fun N =>
    cayley_cfc_sub_norm_sq_integral U hgrp hU0 hUinner hUbd hSC (cayleyExpBump t N) (cayleyExpBump s N)
      (cayleyExpBump_continuousOn U hgrp hU0 hUinner hUbd hSC t N)
      (cayleyExpBump_continuousOn U hgrp hU0 hUinner hUbd hSC s N) x
  -- (C) the L² integral → ∫ ‖e_t − e_s‖² dμ_x  (dominated convergence, η_N² ≤ 1, η_N² → 1 a.e.)
  have hC : Filter.Tendsto (fun N => ∫ ω, ‖cayleyExpBump t N (ω : ℂ) - cayleyExpBump s N (ω : ℂ)‖ ^ 2
        ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x)) Filter.atTop
      (nhds (∫ ω, ‖cayleyExp t (ω : ℂ) - cayleyExp s (ω : ℂ)‖ ^ 2
        ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))) := by
    apply tendsto_integral_of_dominated_convergence (bound := fun _ => (4 : ℝ))
    · intro N
      refine Continuous.aestronglyMeasurable ?_
      exact ((((cayleyExpBump_continuousOn U hgrp hU0 hUinner hUbd hSC t N).comp_continuous
          continuous_subtype_val (fun ω => ω.2)).sub
        ((cayleyExpBump_continuousOn U hgrp hU0 hUinner hUbd hSC s N).comp_continuous
          continuous_subtype_val (fun ω => ω.2))).norm.pow 2)
    · exact integrable_const 4
    · intro N
      filter_upwards with ω
      have hcirc : ‖(ω : ℂ)‖ = 1 := by
        have hmem := cayley_spectrum_subset_circle U hgrp hU0 hUinner hUbd hSC ω.2
        rwa [mem_sphere_zero_iff_norm] at hmem
      rw [Real.norm_of_nonneg (by positivity)]
      have hd : ‖cayleyExpBump t N (ω : ℂ) - cayleyExpBump s N (ω : ℂ)‖ ≤ 2 := by
        calc ‖cayleyExpBump t N (ω : ℂ) - cayleyExpBump s N (ω : ℂ)‖
            ≤ ‖cayleyExpBump t N (ω : ℂ)‖ + ‖cayleyExpBump s N (ω : ℂ)‖ := norm_sub_le _ _
          _ = cayleyBump N (ω : ℂ) + cayleyBump N (ω : ℂ) := by
              rw [cayleyExpBump_norm t N hcirc, cayleyExpBump_norm s N hcirc]
          _ ≤ 2 := by nlinarith [cayleyBump_le_one N (ω : ℂ), cayleyBump_nonneg N (ω : ℂ)]
      nlinarith [hd, norm_nonneg (cayleyExpBump t N (ω : ℂ) - cayleyExpBump s N (ω : ℂ))]
    · have hnull : ∀ᵐ (ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H))
          ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x), (ω : ℂ) ≠ 1 := by
        rw [ae_iff]; simp only [not_ne_iff]
        exact cayleyScalarMeasure_atom_eq_zero U hgrp hU0 hUinner hUbd hSC x
      filter_upwards [hnull] with ω hω
      have hfac : ∀ N, ‖cayleyExpBump t N (ω : ℂ) - cayleyExpBump s N (ω : ℂ)‖ ^ 2
          = (cayleyBump N (ω : ℂ)) ^ 2 * ‖cayleyExp t (ω : ℂ) - cayleyExp s (ω : ℂ)‖ ^ 2 := by
        intro N
        have he : cayleyExpBump t N (ω : ℂ) - cayleyExpBump s N (ω : ℂ)
            = (cayleyBump N (ω : ℂ) : ℂ) * (cayleyExp t (ω : ℂ) - cayleyExp s (ω : ℂ)) := by
          simp only [cayleyExpBump]; ring
        rw [he, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (cayleyBump_nonneg N _)]
      simp only [hfac]
      have hb1 : Filter.Tendsto (fun N => cayleyBump N (ω : ℂ)) Filter.atTop (nhds 1) := by
        have h : Filter.Tendsto (fun N => 1 - cayleyCutoff N (ω : ℂ)) Filter.atTop (nhds (1 - 0)) :=
          tendsto_const_nhds.sub (cayleyCutoff_tendsto_zero_of_ne hω)
        simpa [cayleyBump] using h
      have hlim := (hb1.pow 2).mul_const (‖cayleyExp t (ω : ℂ) - cayleyExp s (ω : ℂ)‖ ^ 2)
      simpa using hlim
  simp only [hB] at hA
  exact tendsto_nhds_unique hA hC

/-- **The Stone symbol is Borel measurable.**  `cayleyExp t ω = exp(i·t·c(ω))` with `c(ω) = i(1+ω)/(1−ω)` is built
    from continuous operations and a complex division, hence Borel measurable on all of `ℂ` (the singularity at the
    excluded point `1` is a single point, harmless for measurability).  This supplies the `AEStronglyMeasurable`
    hypothesis for the strong-continuity dominated-convergence pass, where the bump form is unavailable. -/
theorem cayleyExp_measurable (t : ℝ) : Measurable (cayleyExp t) := by
  have hinv : Measurable cayleyInv := by
    unfold cayleyInv
    exact (measurable_const.mul (measurable_const.add measurable_id)).div (measurable_const.sub measurable_id)
  unfold cayleyExp
  exact Complex.continuous_exp.measurable.comp (measurable_const.mul (measurable_const.mul hinv))

/-- **★★★★★ STRONG CONTINUITY of the Stone group:** `t ↦ U_t x` is continuous.  By the limit Parseval
    (`cayleyStoneU_sub_norm_sq`), `‖U_t x − U_s x‖ = √(∫ ‖e_t − e_s‖² dμ_x)`, and the integral `→ 0` as `t → s` by
    dominated convergence (`tendsto_integral_filter_of_dominated_convergence` on the countably-generated filter
    `𝓝 s`): for each `ω`, `e_t(ω) = exp(i·t·c(ω))` is continuous in `t` so `‖e_t − e_s‖² → 0`, dominated by `4`
    (`‖e_r‖ = 1` on `σ(V) ⊆ S¹`).  So `‖U_t x − U_s x‖ → 0`, i.e. `U_t x → U_s x`.  With the group law and the
    isometry, this is the last analytic ingredient of Stone's theorem: `t ↦ U_t` is a **strongly continuous
    one-parameter group of unitaries**.  Axiom-free; free scalar; no UV datum. -/
theorem cayleyStoneU_continuous [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (x : H) :
    Continuous (fun t => cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x) := by
  haveI : IsFiniteMeasure (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x) :=
    cayleyScalarMeasure_isFiniteMeasure U hgrp hU0 hUinner hUbd hSC x
  refine continuous_iff_continuousAt.mpr (fun s => ?_)
  -- the symbol-difference integral tends to 0 as t → s (dominated convergence on 𝓝 s)
  have hint : Filter.Tendsto (fun t => ∫ ω, ‖cayleyExp t (ω : ℂ) - cayleyExp s (ω : ℂ)‖ ^ 2
      ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x)) (nhds s)
      (nhds (∫ _ω, (0 : ℝ) ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))) := by
    apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ => (4 : ℝ))
    · refine Filter.Eventually.of_forall (fun t => ?_)
      refine Measurable.aestronglyMeasurable ?_
      exact ((((cayleyExp_measurable t).comp measurable_subtype_coe).sub
        ((cayleyExp_measurable s).comp measurable_subtype_coe)).norm.pow_const 2)
    · refine Filter.Eventually.of_forall (fun t => ?_)
      filter_upwards with ω
      have hcirc : ‖(ω : ℂ)‖ = 1 := by
        have hmem := cayley_spectrum_subset_circle U hgrp hU0 hUinner hUbd hSC ω.2
        rwa [mem_sphere_zero_iff_norm] at hmem
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have hd : ‖cayleyExp t (ω : ℂ) - cayleyExp s (ω : ℂ)‖ ≤ 2 := by
        calc ‖cayleyExp t (ω : ℂ) - cayleyExp s (ω : ℂ)‖
            ≤ ‖cayleyExp t (ω : ℂ)‖ + ‖cayleyExp s (ω : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [cayleyExp_abs_circle hcirc, cayleyExp_abs_circle hcirc]; norm_num
      nlinarith [hd, norm_nonneg (cayleyExp t (ω : ℂ) - cayleyExp s (ω : ℂ))]
    · exact integrable_const 4
    · filter_upwards with ω
      have hcont : Continuous (fun r : ℝ => cayleyExp r (ω : ℂ)) := by
        simp only [cayleyExp]
        exact Complex.continuous_exp.comp
          (continuous_const.mul (Complex.continuous_ofReal.mul continuous_const))
      have h2 := (((hcont.tendsto s).sub
        (tendsto_const_nhds (x := cayleyExp s (ω : ℂ)))).norm).pow 2
      simpa using h2
  rw [integral_zero] at hint
  -- ‖U_t x − U_s x‖ = √(∫ ‖e_t − e_s‖²) → √0 = 0, so U_t x → U_s x
  have heq : (fun t => ‖cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x
        - cayleyStoneU U hgrp hU0 hUinner hUbd hSC s x‖)
      = (fun t => Real.sqrt (∫ ω, ‖cayleyExp t (ω : ℂ) - cayleyExp s (ω : ℂ)‖ ^ 2
          ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC x))) := by
    funext t
    rw [← cayleyStoneU_sub_norm_sq U hgrp hU0 hUinner hUbd hSC s t x]
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  have hnorm : Filter.Tendsto (fun t => ‖cayleyStoneU U hgrp hU0 hUinner hUbd hSC t x
      - cayleyStoneU U hgrp hU0 hUinner hUbd hSC s x‖) (nhds s) (nhds 0) := by
    rw [heq]
    have h := (Real.continuous_sqrt.tendsto 0).comp hint
    rwa [Real.sqrt_zero] at h
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  exact hnorm

/-- **The Stone group commutes with the Cayley unitary `V`:** `U_t (V y) = V (U_t y)`.  Each cutoff operator
    `cfc(g_{t,N}) V` commutes with `V` (it is a continuous function of `V`, so they lie in the same abelian algebra —
    `Commute.cfc`); passing to the strong limit (both `cfc(g_{t,N}) V (V y) → U_t(V y)` and, by continuity of `V`,
    `V (cfc(g_{t,N}) V y) → V(U_t y)`) gives `U_t V = V U_t`.  Thus `U_t = exp(it A)` is a **function of `V`** — it
    lies in the abelian von Neumann algebra generated by the Cayley unitary, the precise sense in which the modular
    flow is generated by its own spectral data.  Axiom-free; free scalar; no UV datum. -/
theorem cayleyStoneU_comm_cayleyUnitary [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (t : ℝ) (y : H) :
    cayleyStoneU U hgrp hU0 hUinner hUbd hSC t
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC y)
      = cayleyUnitary U hgrp hU0 hUinner hUbd hSC
        (cayleyStoneU U hgrp hU0 hUinner hUbd hSC t y) := by
  -- each cutoff operator commutes with `V`
  have hcommN : ∀ N, cfc (cayleyExpBump t N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
        ((cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) y)
      = (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
        (cfc (cayleyExpBump t N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) y) := by
    intro N
    have hc : Commute (cfc (cayleyExpBump t N)
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H))
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) :=
      (Commute.refl _).cfc (cayley_isStarNormal U hgrp hU0 hUinner hUbd hSC).star_comm_self
        (cayleyExpBump t N)
    calc cfc (cayleyExpBump t N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
            ((cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) y)
        = (cfc (cayleyExpBump t N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
            * (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) y :=
          (ContinuousLinearMap.mul_apply _ _ _).symm
      _ = ((cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
            * cfc (cayleyExpBump t N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) y := by
          rw [hc.eq]
      _ = (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
            (cfc (cayleyExpBump t N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) y) :=
          ContinuousLinearMap.mul_apply _ _ _
  -- pass to the strong limit on both sides
  have hL := cayleyStoneU_tendsto U hgrp hU0 hUinner hUbd hSC t
    ((cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) y)
  have hR := ((cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H).continuous.tendsto
    (cayleyStoneU U hgrp hU0 hUinner hUbd hSC t y)).comp
    (cayleyStoneU_tendsto U hgrp hU0 hUinner hUbd hSC t y)
  have heq : (fun N => cfc (cayleyExpBump t N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
        ((cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) y))
      = (fun N => (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
          (cfc (cayleyExpBump t N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) y)) := by
    funext N; exact hcommN N
  rw [heq] at hL
  exact tendsto_nhds_unique hL hR

/-- **★★★★ The spectral action of the Stone group on the cfc core:** `U_t (cfc φ V z) = cfc(e_t·φ) V z`.  On the
    spectral-calculus vectors `cfc φ V z` (with `φ` and every `e_t·φ` continuous on `σ(V)` — e.g. `φ` vanishing at the
    excluded point `1`, so the symbol stays continuous), the abstract strong-limit group `U_t` acts by **multiplying
    the symbol by `e_t(ω) = exp(it·c(ω))`**.  Proof: `cfc(g_{t,N}) V (cfc φ V z) = cfc(g_{t,N}·φ) V z` (`cfc_mul`),
    `→ U_t(cfc φ V z)` (`cayleyStoneU_tendsto`); and `cfc(g_{t,N}·φ) V z → cfc(e_t·φ) V z` since the `L²`-defect is
    `∫ ‖(g_{t,N} − e_t)φ‖² = ∫ ψ_N²|φ|² ≤ M²∫ ψ_N² → 0` (`cayley_cfc_sub_norm_sq_integral` +
    `cayleyExpBump_sub_norm` + `cayleyCutoff_sq_integral_tendsto_zero`, `M` the sup of `|φ|` on the compact `σ(V)`);
    uniqueness.  This identifies the abstract `U_t` with the **bounded-Borel functional calculus `cfc(e_t·)`** on a
    core — the concrete spectral meaning of `U_t = exp(it A)`, and the gateway to differentiating `t ↦ U_t (cfc φ V z)`
    to read off the generator.  Axiom-free; free scalar; no UV datum. -/
theorem cayleyStoneU_cfc [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (φ : ℂ → ℂ)
    (hφ : ContinuousOn φ (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)))
    (hetφ : ∀ r : ℝ, ContinuousOn (fun ω => cayleyExp r ω * φ ω)
      (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H))) (t : ℝ) (z : H) :
    cayleyStoneU U hgrp hU0 hUinner hUbd hSC t
        (cfc φ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z)
      = cfc (fun ω => cayleyExp t ω * φ ω)
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z := by
  haveI : IsFiniteMeasure (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC z) :=
    cayleyScalarMeasure_isFiniteMeasure U hgrp hU0 hUinner hUbd hSC z
  obtain ⟨M, hM⟩ := (cayley_spectrum_isCompact U hgrp hU0 hUinner hUbd hSC).exists_bound_of_continuousOn hφ
  -- `U_t (cfc φ V z)` is the strong limit of `cfc(g_{t,N}·φ) V z`
  have hmul : ∀ N, cfc (cayleyExpBump t N) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
        (cfc φ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z)
      = cfc (fun ω => cayleyExpBump t N ω * φ ω)
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z := by
    intro N
    rw [← ContinuousLinearMap.mul_apply,
      ← cfc_mul (cayleyExpBump t N) φ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
        (cayleyExpBump_continuousOn U hgrp hU0 hUinner hUbd hSC t N) hφ]
  have hL : Filter.Tendsto (fun N => cfc (fun ω => cayleyExpBump t N ω * φ ω)
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z) Filter.atTop
      (nhds (cayleyStoneU U hgrp hU0 hUinner hUbd hSC t
        (cfc φ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z))) := by
    have h := cayleyStoneU_tendsto U hgrp hU0 hUinner hUbd hSC t
      (cfc φ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z)
    simpa only [hmul] using h
  -- `cfc(g_{t,N}·φ) V z → cfc(e_t·φ) V z` in `L²` hence strongly
  have hdiff : Filter.Tendsto (fun N => cfc (fun ω => cayleyExpBump t N ω * φ ω)
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z
      - cfc (fun ω => cayleyExp t ω * φ ω)
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hψsq := cayleyCutoff_sq_integral_tendsto_zero U hgrp hU0 hUinner hUbd hSC z
    have hsqrt : Filter.Tendsto (fun N => Real.sqrt (M ^ 2 * ∫ ω, (cayleyCutoff N (ω : ℂ)) ^ 2
        ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC z))) Filter.atTop (nhds 0) := by
      have h := (Real.continuous_sqrt.tendsto (M ^ 2 * 0)).comp (hψsq.const_mul (M ^ 2))
      simpa using h
    have hint2 : ∀ N, Integrable (fun ω : spectrum ℂ
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) => (cayleyCutoff N (ω : ℂ)) ^ 2)
        (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC z) := by
      intro N
      refine (integrable_const (1 : ℝ)).mono' ?_ ?_
      · exact (((cayleyCutoff_continuous N).comp continuous_subtype_val).pow 2).aestronglyMeasurable
      · filter_upwards with ω
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        nlinarith [(cayleyCutoff_pos N (ω : ℂ)).le, cayleyCutoff_le_one N (ω : ℂ)]
    refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hsqrt
    have hb : ‖cfc (fun ω => cayleyExpBump t N ω * φ ω)
          (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z
        - cfc (fun ω => cayleyExp t ω * φ ω)
          (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z‖ ^ 2
        ≤ M ^ 2 * ∫ ω, (cayleyCutoff N (ω : ℂ)) ^ 2
          ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC z) := by
      rw [cayley_cfc_sub_norm_sq_integral U hgrp hU0 hUinner hUbd hSC
          (fun ω => cayleyExpBump t N ω * φ ω) (fun ω => cayleyExp t ω * φ ω)
          ((cayleyExpBump_continuousOn U hgrp hU0 hUinner hUbd hSC t N).mul hφ) (hetφ t) z,
        ← integral_const_mul]
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ω => sq_nonneg _))
        ((hint2 N).const_mul (M ^ 2))
      filter_upwards with ω
      have hcirc : ‖(ω : ℂ)‖ = 1 := by
        have hmem := cayley_spectrum_subset_circle U hgrp hU0 hUinner hUbd hSC ω.2
        rwa [mem_sphere_zero_iff_norm] at hmem
      have hfac : cayleyExpBump t N (ω : ℂ) * φ (ω : ℂ) - cayleyExp t (ω : ℂ) * φ (ω : ℂ)
          = (cayleyExpBump t N (ω : ℂ) - cayleyExp t (ω : ℂ)) * φ (ω : ℂ) := by ring
      have hsub : ‖cayleyExpBump t N (ω : ℂ) - cayleyExp t (ω : ℂ)‖ = cayleyCutoff N (ω : ℂ) := by
        simpa only [cayleyExpBump] using cayleyExpBump_sub_norm t N hcirc
      rw [hfac, norm_mul, mul_pow, hsub]
      have hφ2 : ‖φ (ω : ℂ)‖ ^ 2 ≤ M ^ 2 := by
        nlinarith [hM (ω : ℂ) ω.2, norm_nonneg (φ (ω : ℂ))]
      nlinarith [mul_le_mul_of_nonneg_left hφ2 (sq_nonneg (cayleyCutoff N (ω : ℂ)))]
    calc ‖cfc (fun ω => cayleyExpBump t N ω * φ ω)
            (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z
          - cfc (fun ω => cayleyExp t ω * φ ω)
            (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z‖
        = Real.sqrt (‖cfc (fun ω => cayleyExpBump t N ω * φ ω)
            (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z
          - cfc (fun ω => cayleyExp t ω * φ ω)
            (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (M ^ 2 * ∫ ω, (cayleyCutoff N (ω : ℂ)) ^ 2
            ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC z)) := Real.sqrt_le_sqrt hb
  have hL2 : Filter.Tendsto (fun N => cfc (fun ω => cayleyExpBump t N ω * φ ω)
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z) Filter.atTop
      (nhds (cfc (fun ω => cayleyExp t ω * φ ω)
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z)) := by
    have h := hdiff.add (tendsto_const_nhds (x := cfc (fun ω => cayleyExp t ω * φ ω)
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z))
    simpa using h
  exact tendsto_nhds_unique hL hL2

/-- **The pointwise `t`-derivative of the Stone symbol at `0`:** `d/dt e_t(ω)|₀ = i·c(ω)`, where
    `e_t(ω) = cayleyExp t ω = exp(i·t·c(ω))` and `c(ω) = cayleyInv ω` is the spectral value.  Since `e_0 = 1`, the
    derivative is exactly `i·c(ω)` (no exponential factor).  This is the pointwise building block of the generator:
    on the cfc core (`cayleyStoneU_cfc`) `U_t(cfc φ V z) = cfc(e_t·φ) V z`, so formally
    `d/dt U_t(cfc φ V z)|₀ = cfc(i·c·φ) V z = i·(A acting on cfc φ V z)` — the generator `A` is multiplication by
    the spectral value `c(ω)`.  (Transferring this pointwise derivative through `cfc` in the parameter `t`, uniformly
    on `σ(V)`, is the remaining analytic step.) -/
theorem cayleyExp_hasDerivAt_zero (ω : ℂ) :
    HasDerivAt (fun t => cayleyExp t ω) (Complex.I * cayleyInv ω) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => (↑t : ℂ)) 1 0 := by
    simpa using Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => (↑t : ℂ) * cayleyInv ω) (cayleyInv ω) 0 := by
    simpa using h1.mul_const (cayleyInv ω)
  have h3 : HasDerivAt (fun t : ℝ => Complex.I * ((↑t : ℂ) * cayleyInv ω))
      (Complex.I * cayleyInv ω) 0 := h2.const_mul Complex.I
  simpa [cayleyExp] using h3.cexp

/-- **The pointwise `t`-derivative of the Stone symbol everywhere:** `d/dt e_t(ω)|ₛ = e_s(ω)·i·c(ω)`.  The
    one-parameter-group form of `cayleyExp_hasDerivAt_zero` (which is the `s = 0` case, `e_0 = 1`).  This says each
    spectral fibre `t ↦ e_t(ω)` solves the scalar ODE `f' = (i·c)·f` — the fibrewise infinitesimal generator is
    multiplication by `i·c(ω)`, exactly the spectral form of `i·A`. -/
theorem cayleyExp_hasDerivAt (s : ℝ) (ω : ℂ) :
    HasDerivAt (fun t => cayleyExp t ω) (cayleyExp s ω * (Complex.I * cayleyInv ω)) s := by
  have h1 : HasDerivAt (fun t : ℝ => (↑t : ℂ)) 1 s := by
    simpa using Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => (↑t : ℂ) * cayleyInv ω) (cayleyInv ω) s := by
    simpa using h1.mul_const (cayleyInv ω)
  have h3 : HasDerivAt (fun t : ℝ => Complex.I * ((↑t : ℂ) * cayleyInv ω))
      (Complex.I * cayleyInv ω) s := h2.const_mul Complex.I
  simpa [cayleyExp] using h3.cexp

/-- **The difference quotient of the Stone symbol converges to its derivative:**
    `(e_t(ω) − 1)/t → i·c(ω)` as `t → 0` (`t ≠ 0`).  Immediate from `cayleyExp_hasDerivAt_zero` via
    `hasDerivAt_iff_tendsto_slope` (the slope at `0` is `t⁻¹•(e_t(ω) − e_0(ω)) = (e_t(ω) − 1)/t`, since `e_0 = 1`).
    This is the **pointwise convergence** the generator's dominated-convergence pass consumes. -/
theorem cayleyExp_slope_tendsto (ω : ℂ) :
    Filter.Tendsto (fun t : ℝ => (cayleyExp t ω - 1) / (t : ℂ))
      (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ) (nhds (Complex.I * cayleyInv ω)) := by
  have h := hasDerivAt_iff_tendsto_slope.mp (cayleyExp_hasDerivAt_zero ω)
  refine Filter.Tendsto.congr' ?_ h
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  rw [slope_def_module, sub_zero, cayleyExp_zero, Complex.real_smul, Complex.ofReal_inv]
  rw [div_eq_mul_inv, mul_comm]

/-- **A `t`-independent bound on the Stone-symbol increment over `σ(V)`:** for `ω` on the unit circle (minus the
    excluded point `1`), `‖e_t(ω) − 1‖ ≤ |t|·‖c(ω)‖`.  On `σ(V) ⊆ S¹` the spectral value `c(ω) = cayleyInv ω` is
    **real** (`cayleyInv_im_eq_zero`), so `e_t(ω) = exp(i·↑(t·c.re))` lies on the unit circle and
    `‖exp(iθ) − 1‖ ≤ |θ|` (`Complex.norm_exp_I_mul_ofReal_sub_one_le`) gives the bound.  Hence
    `‖(e_t(ω) − 1)/t‖ ≤ ‖c(ω)‖` — the uniform dominating function the generator's dominated-convergence pass needs
    (it makes the difference quotients dominated by `‖c·φ‖`, integrable on a core where `c·φ` is bounded). -/
theorem cayleyExp_sub_one_norm_le {ω : ℂ} (h1 : ‖ω‖ = 1) (hne : ω ≠ 1) (t : ℝ) :
    ‖cayleyExp t ω - 1‖ ≤ |t| * ‖cayleyInv ω‖ := by
  have hc : cayleyInv ω = ((cayleyInv ω).re : ℂ) := by
    apply Complex.ext <;> simp [cayleyInv_im_eq_zero h1 hne]
  have hnorm : ‖cayleyInv ω‖ = |(cayleyInv ω).re| := by
    conv_lhs => rw [hc]
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hrw : cayleyExp t ω = Complex.exp (Complex.I * ((t * (cayleyInv ω).re : ℝ) : ℂ)) := by
    rw [cayleyExp]
    congr 2
    conv_lhs => rw [hc]
    push_cast
    ring
  rw [hrw]
  calc ‖Complex.exp (Complex.I * ((t * (cayleyInv ω).re : ℝ) : ℂ)) - 1‖
      ≤ ‖t * (cayleyInv ω).re‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = |t| * ‖cayleyInv ω‖ := by rw [Real.norm_eq_abs, abs_mul, hnorm]

/-- **The inverse-Cayley map is Borel measurable** (`c(ω) = i(1+ω)/(1−ω)`: continuous operations + a complex
    division).  Supplies the measurability of the generator's difference-quotient integrand, where `c` appears
    standalone (not protected by `φ`). -/
theorem cayleyInv_measurable : Measurable cayleyInv := by
  unfold cayleyInv
  exact (measurable_const.mul (measurable_const.add measurable_id)).div
    (measurable_const.sub measurable_id)

/-- **★★★★★ The scalar generator dominated-convergence pass** (the analytic heart of the generator):
    `∫ ‖((e_τ − 1)/τ − i·c)·φ‖² dμ_z → 0` as `τ → 0` (`τ ≠ 0`), for `φ` and `c·φ` continuous on `σ(V)`.  This is the
    squared `L²(μ_z)`-norm of the difference between the symbol difference quotient `(e_τ·φ − φ)/τ` and its formal
    limit `i·c·φ`, and it vanishes by dominated convergence on the countably-generated filter `𝓝[≠] 0`: the integrand
    `→ 0` `μ_z`-a.e. (`cayleyExp_slope_tendsto`: `(e_τ − 1)/τ → i·c`), and is dominated by `4‖c·φ‖²` (integrable,
    since `c·φ ∈ C(σV)` is bounded on the compact `σ(V)`) because `‖(e_τ − 1)/τ‖ ≤ ‖c‖` on `σ(V) ⊆ S¹`
    (`cayleyExp_sub_one_norm_le`).  Combined with Parseval (`‖cfc(s_τ) V z‖² = ∫‖s_τ‖²dμ_z`) and the cfc-algebra, this
    yields `HasDerivAt (t ↦ U_t(cfc φ V z)) (i·cfc(c·φ) V z) 0` — the generator on the cfc core.  Axiom-free. -/
theorem cayleyExp_gen_integrand_tendsto [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (φ : ℂ → ℂ)
    (hφ : ContinuousOn φ (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)))
    (hcφ : ContinuousOn (fun ω => cayleyInv ω * φ ω)
      (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H))) (z : H) :
    Filter.Tendsto (fun τ : ℝ => ∫ ω, ‖((cayleyExp τ (ω : ℂ) - 1) / (τ : ℂ)
        - Complex.I * cayleyInv (ω : ℂ)) * φ (ω : ℂ)‖ ^ 2
      ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC z))
      (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ) (nhds 0) := by
  haveI : IsFiniteMeasure (cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC z) :=
    cayleyScalarMeasure_isFiniteMeasure U hgrp hU0 hUinner hUbd hSC z
  have hnull : ∀ᵐ (ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H))
      ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC z), (ω : ℂ) ≠ 1 := by
    rw [ae_iff]; simp only [not_ne_iff]
    exact cayleyScalarMeasure_atom_eq_zero U hgrp hU0 hUinner hUbd hSC z
  have hφm : Measurable (fun ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
      => φ (ω : ℂ)) :=
    (hφ.comp_continuous continuous_subtype_val (fun ω => ω.2)).measurable
  suffices hconv : Filter.Tendsto (fun τ : ℝ => ∫ ω, ‖((cayleyExp τ (ω : ℂ) - 1) / (τ : ℂ)
        - Complex.I * cayleyInv (ω : ℂ)) * φ (ω : ℂ)‖ ^ 2
      ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC z))
      (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ)
      (nhds (∫ _ω, (0 : ℝ) ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC z))) by
    rwa [integral_zero] at hconv
  refine tendsto_integral_filter_of_dominated_convergence
    (F := fun (τ : ℝ) (ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) =>
      ‖((cayleyExp τ (ω : ℂ) - 1) / (τ : ℂ) - Complex.I * cayleyInv (ω : ℂ)) * φ (ω : ℂ)‖ ^ 2)
    (f := fun _ => (0 : ℝ)) (bound := fun ω => 4 * ‖cayleyInv (ω : ℂ) * φ (ω : ℂ)‖ ^ 2) ?_ ?_ ?_ ?_
  · -- AEStronglyMeasurable of each integrand
    filter_upwards with τ
    refine Measurable.aestronglyMeasurable ?_
    have hem : Measurable (fun ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
        => cayleyExp τ (ω : ℂ)) := (cayleyExp_measurable τ).comp measurable_subtype_coe
    have hcm : Measurable (fun ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
        => cayleyInv (ω : ℂ)) := cayleyInv_measurable.comp measurable_subtype_coe
    exact ((((hem.sub measurable_const).div measurable_const).sub
      (measurable_const.mul hcm)).mul hφm).norm.pow_const 2
  · -- domination
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    filter_upwards [hnull] with ω hω
    have hτ0 : τ ≠ 0 := hτ
    have hcirc : ‖(ω : ℂ)‖ = 1 := by
      have hmem := cayley_spectrum_subset_circle U hgrp hU0 hUinner hUbd hSC ω.2
      rwa [mem_sphere_zero_iff_norm] at hmem
    rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
    have hb : ‖(cayleyExp τ (ω : ℂ) - 1) / (τ : ℂ) - Complex.I * cayleyInv (ω : ℂ)‖
        ≤ 2 * ‖cayleyInv (ω : ℂ)‖ := by
      calc ‖(cayleyExp τ (ω : ℂ) - 1) / (τ : ℂ) - Complex.I * cayleyInv (ω : ℂ)‖
          ≤ ‖(cayleyExp τ (ω : ℂ) - 1) / (τ : ℂ)‖ + ‖Complex.I * cayleyInv (ω : ℂ)‖ := norm_sub_le _ _
        _ ≤ ‖cayleyInv (ω : ℂ)‖ + ‖cayleyInv (ω : ℂ)‖ := by
            gcongr
            · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ (abs_pos.mpr hτ0), mul_comm]
              exact cayleyExp_sub_one_norm_le hcirc hω τ
            · rw [norm_mul, Complex.norm_I, one_mul]
        _ = 2 * ‖cayleyInv (ω : ℂ)‖ := by ring
    have hd := norm_nonneg ((cayleyExp τ (ω : ℂ) - 1) / (τ : ℂ) - Complex.I * cayleyInv (ω : ℂ))
    have hsq : ‖(cayleyExp τ (ω : ℂ) - 1) / (τ : ℂ) - Complex.I * cayleyInv (ω : ℂ)‖ ^ 2
        ≤ 4 * ‖cayleyInv (ω : ℂ)‖ ^ 2 := by nlinarith [hb, hd, norm_nonneg (cayleyInv (ω : ℂ))]
    have hcφnorm : ‖cayleyInv (ω : ℂ) * φ (ω : ℂ)‖ ^ 2
        = ‖cayleyInv (ω : ℂ)‖ ^ 2 * ‖φ (ω : ℂ)‖ ^ 2 := by rw [norm_mul, mul_pow]
    rw [hcφnorm]
    nlinarith [hsq, sq_nonneg ‖φ (ω : ℂ)‖, norm_nonneg (cayleyInv (ω : ℂ))]
  · -- bound integrable: `4‖c·φ‖²` is continuous on the compact `σ(V)`, hence bounded, hence integrable
    obtain ⟨M, hM⟩ := (cayley_spectrum_isCompact U hgrp hU0 hUinner hUbd hSC).exists_bound_of_continuousOn hcφ
    have hcont : Continuous (fun ω : spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
        => cayleyInv (ω : ℂ) * φ (ω : ℂ)) :=
      hcφ.comp_continuous continuous_subtype_val (fun ω => ω.2)
    refine (integrable_const (4 * M ^ 2)).mono' ?_ ?_
    · exact (continuous_const.mul (hcont.norm.pow 2)).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_of_nonneg (by positivity)]
      nlinarith [hM (ω : ℂ) ω.2, norm_nonneg (cayleyInv (ω : ℂ) * φ (ω : ℂ))]
  · -- pointwise limit a.e.
    filter_upwards with ω
    have hsl := cayleyExp_slope_tendsto (ω : ℂ)
    have h0 : Filter.Tendsto (fun τ : ℝ => (cayleyExp τ (ω : ℂ) - 1) / (τ : ℂ)
        - Complex.I * cayleyInv (ω : ℂ)) (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ) (nhds 0) := by
      have := hsl.sub_const (Complex.I * cayleyInv (ω : ℂ))
      simpa using this
    have h1 := ((h0.mul_const (φ (ω : ℂ))).norm).pow 2
    simpa using h1

/-- **The operator difference-quotient as a single cfc, with its `L²` norm** (the cfc-algebra bridge from the scalar
    generator DCT to the operator generator):
    `‖τ⁻¹·(cfc(e_τ·φ) V z − cfc φ V z) − i·cfc(c·φ) V z‖² = ∫ ‖((e_τ−1)/τ − i·c)·φ‖² dμ_z`.
    The left vector equals `cfc(s_τ) V z` with `s_τ = τ⁻¹·(e_τ·φ − φ) − i·(c·φ)` (`cfc_sub` + `cfc_const_mul`); its
    squared norm is `∫‖s_τ‖²dμ_z` (Parseval, `cayley_cfc_norm_sq_integral`), and `s_τ(ω) = ((e_τ−1)/τ − i·c)·φ`
    pointwise (`ring`), matching the integrand of `cayleyExp_gen_integrand_tendsto`.  This is the last operator-side
    bookkeeping before the generator `HasDerivAt`.  Axiom-free. -/
theorem cayleyStoneU_slope_norm_sq [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (φ : ℂ → ℂ)
    (hφ : ContinuousOn φ (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)))
    (hetφ : ∀ r : ℝ, ContinuousOn (fun ω => cayleyExp r ω * φ ω)
      (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)))
    (hcφ : ContinuousOn (fun ω => cayleyInv ω * φ ω)
      (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H))) (τ : ℝ) (z : H) :
    ‖(τ : ℂ)⁻¹ • (cfc (fun ω => cayleyExp τ ω * φ ω)
            (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z
          - cfc φ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z)
        - Complex.I • cfc (fun ω => cayleyInv ω * φ ω)
          (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z‖ ^ 2
      = ∫ ω, ‖((cayleyExp τ (ω : ℂ) - 1) / (τ : ℂ) - Complex.I * cayleyInv (ω : ℂ)) * φ (ω : ℂ)‖ ^ 2
        ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC z) := by
  -- the operator identity: `cfc s_τ V = τ⁻¹ • (cfc(e_τφ) V − cfc φ V) − i • cfc(c·φ) V`
  have hop : cfc (fun ω => (τ : ℂ)⁻¹ * (cayleyExp τ ω * φ ω - φ ω) - Complex.I * (cayleyInv ω * φ ω))
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
      = (τ : ℂ)⁻¹ • (cfc (fun ω => cayleyExp τ ω * φ ω)
            (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
          - cfc φ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H))
        - Complex.I • cfc (fun ω => cayleyInv ω * φ ω)
          (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) := by
    rw [cfc_sub (fun ω => (τ : ℂ)⁻¹ * (cayleyExp τ ω * φ ω - φ ω))
        (fun ω => Complex.I * (cayleyInv ω * φ ω))
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
        (continuousOn_const.mul ((hetφ τ).sub hφ)) (continuousOn_const.mul hcφ),
      cfc_const_mul (τ : ℂ)⁻¹ (fun ω => cayleyExp τ ω * φ ω - φ ω)
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) ((hetφ τ).sub hφ),
      cfc_const_mul Complex.I (fun ω => cayleyInv ω * φ ω)
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) hcφ,
      cfc_sub (fun ω => cayleyExp τ ω * φ ω) φ
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) (hetφ τ) hφ]
  -- apply to `z`
  have hvec : (τ : ℂ)⁻¹ • (cfc (fun ω => cayleyExp τ ω * φ ω)
          (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z
        - cfc φ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z)
      - Complex.I • cfc (fun ω => cayleyInv ω * φ ω)
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z
      = cfc (fun ω => (τ : ℂ)⁻¹ * (cayleyExp τ ω * φ ω - φ ω) - Complex.I * (cayleyInv ω * φ ω))
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z := by
    rw [hop]; simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply]
  rw [hvec, cayley_cfc_norm_sq_integral U hgrp hU0 hUinner hUbd hSC
    (fun ω => (τ : ℂ)⁻¹ * (cayleyExp τ ω * φ ω - φ ω) - Complex.I * (cayleyInv ω * φ ω))
    ((continuousOn_const.mul ((hetφ τ).sub hφ)).sub (continuousOn_const.mul hcφ)) z]
  apply integral_congr_ae
  filter_upwards with ω
  congr 1
  rw [show (τ : ℂ)⁻¹ * (cayleyExp τ (ω : ℂ) * φ (ω : ℂ) - φ (ω : ℂ))
        - Complex.I * (cayleyInv (ω : ℂ) * φ (ω : ℂ))
      = ((cayleyExp τ (ω : ℂ) - 1) / (τ : ℂ) - Complex.I * cayleyInv (ω : ℂ)) * φ (ω : ℂ) from by ring]

/-- **★★★★★ THE GENERATOR ON THE cfc CORE — Stone's converse:**
    `HasDerivAt (t ↦ U_t(cfc φ V z)) (i·cfc(c·φ) V z) 0` for `φ`, `e_r·φ`, `c·φ` continuous on `σ(V)`.
    On the spectral-calculus core, the Stone group `U_t = exp(it A)` is **differentiable in `t`**, and its derivative
    at `0` is `i` times multiplication by the spectral value `c(ω) = cayleyInv ω` — i.e. the **generator `A` is
    multiplication by `c`** (the spectral form of `A = i(1+V)(1−V)⁻¹`).  Proof: rewrite `U_t(cfc φ V z) = cfc(e_t·φ) V z`
    (`cayleyStoneU_cfc`); via `hasDerivAt_iff_tendsto_slope`, the slope minus the claimed derivative has norm `→ 0`,
    because its **square** is `∫‖((e_τ−1)/τ − i·c)·φ‖²dμ_z` (`cayleyStoneU_slope_norm_sq`, the cfc-algebra+Parseval
    bridge) which `→ 0` (`cayleyExp_gen_integrand_tendsto`, the scalar DCT), through `√`-continuity.  Axiom-free; free
    scalar; no UV datum.  This is the converse half of Stone's theorem for the Cayley/cfc construction — the group is
    the exponential of its own generator on a core. -/
theorem cayleyStoneU_cfc_hasDerivAt [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (φ : ℂ → ℂ)
    (hφ : ContinuousOn φ (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)))
    (hetφ : ∀ r : ℝ, ContinuousOn (fun ω => cayleyExp r ω * φ ω)
      (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)))
    (hcφ : ContinuousOn (fun ω => cayleyInv ω * φ ω)
      (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H))) (z : H) :
    HasDerivAt (fun t => cayleyStoneU U hgrp hU0 hUinner hUbd hSC t
        (cfc φ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z))
      (Complex.I • cfc (fun ω => cayleyInv ω * φ ω)
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z) 0 := by
  have hfeq : (fun t => cayleyStoneU U hgrp hU0 hUinner hUbd hSC t
        (cfc φ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z))
      = (fun t => cfc (fun ω => cayleyExp t ω * φ ω)
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z) := by
    funext t; exact cayleyStoneU_cfc U hgrp hU0 hUinner hUbd hSC φ hφ hetφ t z
  have hg0 : cfc (fun ω => cayleyExp (0 : ℝ) ω * φ ω)
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z
      = cfc φ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z := by
    have hsymb : (fun ω => cayleyExp (0 : ℝ) ω * φ ω) = φ := by
      funext ω; rw [cayleyExp_zero, one_mul]
    rw [hsymb]
  rw [hfeq, hasDerivAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  -- the slope minus the claimed derivative, rewritten into the norm²-identity form
  have heq : ∀ τ : ℝ, slope (fun t => cfc (fun ω => cayleyExp t ω * φ ω)
          (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z) 0 τ
        - Complex.I • cfc (fun ω => cayleyInv ω * φ ω)
          (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z
      = (τ : ℂ)⁻¹ • (cfc (fun ω => cayleyExp τ ω * φ ω)
            (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z
          - cfc φ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z)
        - Complex.I • cfc (fun ω => cayleyInv ω * φ ω)
          (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z := by
    intro τ
    rw [slope_def_module, sub_zero, hg0, ← Complex.coe_smul τ⁻¹, Complex.ofReal_inv]
  simp only [heq]
  have heqn : (fun τ : ℝ => ‖(τ : ℂ)⁻¹ • (cfc (fun ω => cayleyExp τ ω * φ ω)
          (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z
        - cfc φ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z)
      - Complex.I • cfc (fun ω => cayleyInv ω * φ ω)
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z‖)
      = (fun τ => Real.sqrt (∫ ω, ‖((cayleyExp τ (ω : ℂ) - 1) / (τ : ℂ)
          - Complex.I * cayleyInv (ω : ℂ)) * φ (ω : ℂ)‖ ^ 2
        ∂(cayleyScalarMeasure U hgrp hU0 hUinner hUbd hSC z))) := by
    funext τ
    rw [← cayleyStoneU_slope_norm_sq U hgrp hU0 hUinner hUbd hSC φ hφ hetφ hcφ τ z,
      Real.sqrt_sq (norm_nonneg _)]
  rw [heqn]
  have h := (Real.continuous_sqrt.tendsto 0).comp
    (cayleyExp_gen_integrand_tendsto U hgrp hU0 hUinner hUbd hSC φ hφ hcφ z)
  rwa [Real.sqrt_zero] at h

/-- **The cfc core lies in the smooth domain of the bundled Stone group:** `cfc φ V z ∈ stoneDomain(cayleyStoneCLM)`.
    Immediate from `cayleyStoneU_cfc_hasDerivAt` (differentiable ⟹ in the domain), through
    `cayleyStoneCLM_apply` (`cayleyStoneCLM … t x = cayleyStoneU … t x`). -/
theorem cayleyStoneCLM_cfc_mem_stoneDomain [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (φ : ℂ → ℂ)
    (hφ : ContinuousOn φ (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)))
    (hetφ : ∀ r : ℝ, ContinuousOn (fun ω => cayleyExp r ω * φ ω)
      (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)))
    (hcφ : ContinuousOn (fun ω => cayleyInv ω * φ ω)
      (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H))) (z : H) :
    cfc φ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z
      ∈ stoneDomain (cayleyStoneCLM U hgrp hU0 hUinner hUbd hSC) := by
  show DifferentiableAt ℝ (fun t => (cayleyStoneCLM U hgrp hU0 hUinner hUbd hSC t)
    (cfc φ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z)) 0
  have heq : (fun t => (cayleyStoneCLM U hgrp hU0 hUinner hUbd hSC t)
        (cfc φ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z))
      = (fun t => cayleyStoneU U hgrp hU0 hUinner hUbd hSC t
        (cfc φ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z)) := by
    funext t; exact cayleyStoneCLM_apply U hgrp hU0 hUinner hUbd hSC t _
  rw [heq]
  exact (cayleyStoneU_cfc_hasDerivAt U hgrp hU0 hUinner hUbd hSC φ hφ hetφ hcφ z).differentiableAt

/-- **★★★★★ THE GENERATOR OF THE STONE GROUP IS MULTIPLICATION BY THE SPECTRAL VALUE** (Stone's correspondence,
    packaged): `stoneGen (cayleyStoneCLM) ⟨cfc φ V z, _⟩ = cfc(c·φ) V z`, where `c(ω) = cayleyInv ω`.  This identifies
    the infinitesimal generator `A x = −i d/dt U_t x|₀` of the reconstructed unitary group with the Cayley-defined
    self-adjoint operator `A = i(1+V)(1−V)⁻¹` acting (via the bounded Borel calculus) on the spectral core: `A` is
    multiplication by `c`.  Wraps `cayleyStoneU_cfc_hasDerivAt` with `stoneGen_eq_of_hasDerivAt` through
    `cayleyStoneCLM_apply`.  This is the precise sense in which **`U_t = exp(it A)` is the Stone group of its own
    generator** — Stone's theorem, both directions, on the cfc core.  Axiom-free; free scalar; no UV datum. -/
theorem cayleyStoneCLM_stoneGen_cfc [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (φ : ℂ → ℂ)
    (hφ : ContinuousOn φ (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)))
    (hetφ : ∀ r : ℝ, ContinuousOn (fun ω => cayleyExp r ω * φ ω)
      (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)))
    (hcφ : ContinuousOn (fun ω => cayleyInv ω * φ ω)
      (spectrum ℂ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H))) (z : H) :
    stoneGen (cayleyStoneCLM U hgrp hU0 hUinner hUbd hSC)
        ⟨cfc φ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z,
          cayleyStoneCLM_cfc_mem_stoneDomain U hgrp hU0 hUinner hUbd hSC φ hφ hetφ hcφ z⟩
      = cfc (fun ω => cayleyInv ω * φ ω) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z := by
  apply stoneGen_eq_of_hasDerivAt
  have heq : (fun t => (cayleyStoneCLM U hgrp hU0 hUinner hUbd hSC t)
        (cfc φ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z))
      = (fun t => cayleyStoneU U hgrp hU0 hUinner hUbd hSC t
        (cfc φ (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z)) := by
    funext t; exact cayleyStoneCLM_apply U hgrp hU0 hUinner hUbd hSC t _
  rw [heq]
  exact cayleyStoneU_cfc_hasDerivAt U hgrp hU0 hUinner hUbd hSC φ hφ hetφ hcφ z

/-- **The cfc bump vectors are an approximate identity:** `cfc(η_N) V z → z`, where `η_N = cayleyBump N`.  Since
    `η_N = 1 − ψ_N`, `cfc(η_N) V z = z − cfc(ψ_N) V z` (`cfc_sub` + `cayley_cfc_one`), and the atom-killing limit
    `cfc(ψ_N) V z → 0` (`cayleyCutoff_cfc_tendsto_zero`, `μ_z({1}) = 0`) gives `z − 0 = z`.  Because each `η_N` is
    continuous on `σ(V)` and vanishes (quadratically) at the excluded point `1` — so the bump vectors `cfc(η_N) V z`
    are genuine spectral-core vectors — this shows the **smooth domain of the Stone group is dense**: every `z` is a
    limit of core vectors on which the generator acts as multiplication by the spectral value `c`.  Axiom-free. -/
theorem cayleyBump_cfc_tendsto [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (z : H) :
    Filter.Tendsto (fun N => cfc (fun ω => (cayleyBump N ω : ℂ))
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z) Filter.atTop (nhds z) := by
  have hrw : (fun N => cfc (fun ω => (cayleyBump N ω : ℂ))
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z)
      = (fun N => z - cfc (fun ω => (cayleyCutoff N ω : ℂ))
        (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H) z) := by
    funext N
    have hsymb : (fun ω => (cayleyBump N ω : ℂ))
        = (fun z => (1 : ℂ → ℂ) z - (fun w => (cayleyCutoff N w : ℂ)) z) := by
      funext ω; simp only [cayleyBump, Pi.one_apply]; push_cast; ring
    rw [hsymb, cfc_sub (f := (1 : ℂ → ℂ)) (g := fun w => (cayleyCutoff N w : ℂ))
        (a := (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H))
        (hg := (Complex.continuous_ofReal.comp (cayleyCutoff_continuous N)).continuousOn),
      cayley_cfc_one U hgrp hU0 hUinner hUbd hSC]
    simp [ContinuousLinearMap.sub_apply]
  rw [hrw]
  have h0 : nhds z = nhds (z - 0) := by rw [sub_zero]
  rw [h0]
  exact tendsto_const_nhds.sub (cayleyCutoff_cfc_tendsto_zero U hgrp hU0 hUinner hUbd hSC z)

/-! ### `cayleyStoneCLM` is itself a `C₀` unitary group

The reconstructed Stone group `t ↦ cayleyStoneCLM U … t` satisfies the five hypotheses of the abstract
strongly-continuous one-parameter unitary group (`hgrp`, `hU0`, `hUinner`, `hUbd`, `hSC`).  This packages it as a
bona-fide input to the Gårding/`stoneGen` machinery (density, the recovery `cayleyStoneCLM U = U`), and lets the
whole Stone construction be iterated/fed back on the reconstructed group. -/

/-- `cayleyStoneCLM … 0 = 1` — the group identity (from `cayleyStoneU_zero`). -/
theorem cayleyStoneCLM_zero [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) :
    cayleyStoneCLM U hgrp hU0 hUinner hUbd hSC 0 = 1 := by
  ext x
  simp only [cayleyStoneCLM_apply, ContinuousLinearMap.one_apply]
  exact cayleyStoneU_zero U hgrp hU0 hUinner hUbd hSC x

/-- `cayleyStoneCLM … (s+t) = cayleyStoneCLM … s ∘L cayleyStoneCLM … t` — the group law (from `cayleyStoneU_group`). -/
theorem cayleyStoneCLM_comp [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (s t : ℝ) :
    cayleyStoneCLM U hgrp hU0 hUinner hUbd hSC (s + t)
      = cayleyStoneCLM U hgrp hU0 hUinner hUbd hSC s ∘L cayleyStoneCLM U hgrp hU0 hUinner hUbd hSC t := by
  ext x
  simp only [cayleyStoneCLM_apply, ContinuousLinearMap.comp_apply]
  exact (cayleyStoneU_group U hgrp hU0 hUinner hUbd hSC s t x).symm

/-- `cayleyStoneCLM … t` preserves the inner product (it is a `LinearIsometryEquiv`, `cayleyStoneLIE`). -/
theorem cayleyStoneCLM_inner [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (t : ℝ) (a b : H) :
    (inner ℂ (cayleyStoneCLM U hgrp hU0 hUinner hUbd hSC t a)
        (cayleyStoneCLM U hgrp hU0 hUinner hUbd hSC t b) : ℂ) = inner ℂ a b := by
  rw [cayleyStoneCLM_apply, cayleyStoneCLM_apply, ← cayleyStoneLIE_apply U hgrp hU0 hUinner hUbd hSC t a,
    ← cayleyStoneLIE_apply U hgrp hU0 hUinner hUbd hSC t b]
  exact LinearIsometryEquiv.inner_map_map (cayleyStoneLIE U hgrp hU0 hUinner hUbd hSC t) a b

/-- `‖cayleyStoneCLM … t y‖ ≤ ‖y‖` — the contraction bound (in fact an isometry, `cayleyStoneCLM_norm_map`). -/
theorem cayleyStoneCLM_norm_le [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (t : ℝ) (y : H) :
    ‖cayleyStoneCLM U hgrp hU0 hUinner hUbd hSC t y‖ ≤ ‖y‖ :=
  (cayleyStoneCLM_norm_map U hgrp hU0 hUinner hUbd hSC t y).le

/-- `t ↦ cayleyStoneCLM … t y` is continuous — strong continuity (from `cayleyStoneU_continuous`). -/
theorem cayleyStoneCLM_continuous [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) (y : H) :
    Continuous (fun t => cayleyStoneCLM U hgrp hU0 hUinner hUbd hSC t y) := by
  have heq : (fun t => cayleyStoneCLM U hgrp hU0 hUinner hUbd hSC t y)
      = (fun t => cayleyStoneU U hgrp hU0 hUinner hUbd hSC t y) := by
    funext t; exact cayleyStoneCLM_apply U hgrp hU0 hUinner hUbd hSC t y
  rw [heq]; exact cayleyStoneU_continuous U hgrp hU0 hUinner hUbd hSC y

/-- **The resolvent symbol's functional calculus:** `cfc((1−ω)/2) V = ½(1 − V)`.  Pure `cfc` linearity
    (`cfc_const_mul` + `cfc_sub` + `cayley_cfc_one` `cfc 1 V = 1` + `cayley_cfc_id` `cfc id V = V`).  Combined with the
    resolvent↔Cayley relation `R = ½(1 − V)` (i.e. `V = 1 − 2R`, to come), this yields `resolvent U = cfc(h) V` with
    `h(ω) = (1−ω)/2` — the bridge that turns `resolvent_stoneGen` (`stoneGen U (R x) = −i(Rx − x)`) into the **direct
    spectral identity** `stoneGen U (cfc φ V z) = cfc(c·φ) V z` (factor `φ = h·ψ`, GPT-5.5-pro route), identifying the
    ORIGINAL group's generator with multiplication by the spectral value `c` — without the recovery / e.s.a. wall. -/
theorem cayley_resolvent_symbol_cfc [Nontrivial H] (U : ℝ → (H →L[ℂ] H))
    (hgrp : ∀ s t, U (s + t) = U s ∘L U t) (hU0 : U 0 = 1)
    (hUinner : ∀ t a b, (inner ℂ (U t a) (U t b) : ℂ) = inner ℂ a b)
    (hUbd : ∀ (t : ℝ) (y : H), ‖U t y‖ ≤ ‖y‖) (hSC : ∀ y : H, Continuous (fun t => U t y)) :
    cfc (fun ω => (1 - ω) / 2 : ℂ → ℂ) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)
      = (2 : ℂ)⁻¹ • ((1 : H →L[ℂ] H) - (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H)) := by
  have hfun : (fun ω : ℂ => (1 - ω) / 2)
      = (fun ω => (2 : ℂ)⁻¹ * ((1 : ℂ → ℂ) ω - (id : ℂ → ℂ) ω)) := by
    funext ω; simp only [Pi.one_apply, id]; ring
  rw [hfun, cfc_const_mul (2 : ℂ)⁻¹ (fun ω => (1 : ℂ → ℂ) ω - (id : ℂ → ℂ) ω)
      (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H),
    cfc_sub (1 : ℂ → ℂ) (id : ℂ → ℂ) (cayleyUnitary U hgrp hU0 hUinner hUbd hSC : H →L[ℂ] H),
    cayley_cfc_one U hgrp hU0 hUinner hUbd hSC, cayley_cfc_id U hgrp hU0 hUinner hUbd hSC]


end SelfAdjoint

end QIQTH.Spectral
