/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Toward Wiener's L² Tauberian theorem (the cyclic Reeh–Schlieder discharge)

The cyclic side of the free-field one-particle Bisognano–Wichmann (`QIQTH.Fock.BoostKMS`,
`niceWedge_isCyclic_of_correlation_total`) reduces to: the boost-orbit (= rapidity translates) of a
single nice generator `g₀ = KrepL2 f₀` is total in `L²(ℝ)` as soon as `𝓕 g₀ ≠ 0` a.e. — this is the L²
**Wiener–Tauberian theorem**.  Mathlib has the integral-level Fourier theory but not the L² translate↔
modulation machinery this needs; we build it here brick by brick.

This file: **Brick 1 — the Schwartz translation operator** `τ_a : f ↦ f(·+a)`.
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Topology
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.Asymptotics
import QIQTH.Fock.OneParticleBW
import QIQTH.Fock.SchwartzDecay

namespace QIQTH.Fock.WienerL2

open SchwartzMap MeasureTheory QIQTH.Fock.OneParticle QIQTH.Fock.OneParticleBW QIQTH.Fock.Localization

/-- **Wiener brick 1 — the Schwartz translation operator** `τ_a : 𝓢(ℝ,ℂ) →L[ℂ] 𝓢(ℝ,ℂ)`, `f ↦ f(·+a)`.
    Built via `SchwartzMap.compCLM` with the temperate-growth affine map `x ↦ x + a` (`HasTemperateGrowth.id'
    + .const`, and the moderate-decay bound `‖x‖ ≤ (1+‖a‖)(1+‖x+a‖)`).  The foundational operator for the
    L²-translate↔modulation intertwining `𝓕 ∘ τ_a = M_a ∘ 𝓕` behind Wiener's L² Tauberian theorem. -/
noncomputable def schwartzTranslate (a : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  compCLM ℂ (g := fun x => x + a)
    (Function.HasTemperateGrowth.id'.add (Function.HasTemperateGrowth.const a))
    ⟨1, 1 + ‖a‖, fun x => by
      rw [pow_one]
      have h2 : ‖x‖ ≤ ‖x + a‖ + ‖a‖ := by
        calc ‖x‖ = ‖(x + a) - a‖ := by ring_nf
          _ ≤ ‖x + a‖ + ‖a‖ := norm_sub_le _ _
      nlinarith [norm_nonneg (x + a), norm_nonneg a]⟩

@[simp] theorem schwartzTranslate_apply (a : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    schwartzTranslate a f x = f (x + a) := by
  rw [schwartzTranslate, compCLM_apply]; rfl

/-- **Wiener brick 3 — the boost unitary IS the Schwartz translation, at `L²`**:
    `boostUnitary a (f.toLp) = (schwartzTranslate (−a) f).toLp` (both `=ᵐ θ ↦ f(θ−a)`, via `coeFn_boostUnitary`,
    the measure-preserving translated-`ae`, and `schwartzTranslate_apply`).  This connects the QIQT rapidity-boost
    group to the generic Schwartz translation, so the Schwartz-level Fourier translate→modulation lemma transfers
    to `boostUnitary` (the next brick toward the intertwining `𝓕 ∘ boostUnitary_a = M_a ∘ 𝓕`). -/
theorem boostUnitary_toLp (a : ℝ) (f : 𝓢(ℝ, ℂ)) :
    boostUnitary a (f.toLp 2 volume) = (schwartzTranslate (-a) f).toLp 2 volume := by
  rw [Lp.ext_iff]
  have e1 : (⇑(boostUnitary a (f.toLp 2 volume)) : ℝ → ℂ)
      =ᵐ[volume] fun θ => (f.toLp 2 volume : ℝ → ℂ) (θ - a) := coeFn_boostUnitary a (f.toLp 2 volume)
  have e2 : (fun θ => (f.toLp 2 volume : ℝ → ℂ) (θ - a)) =ᵐ[volume] fun θ => f (θ - a) :=
    (measurePreserving_sub_right volume a).quasiMeasurePreserving.ae_eq_comp (f.coeFn_toLp 2 volume)
  have e3 : (⇑((schwartzTranslate (-a) f).toLp 2 volume) : ℝ → ℂ) =ᵐ[volume] fun θ => f (θ - a) := by
    refine ((schwartzTranslate (-a) f).coeFn_toLp 2 volume).trans ?_
    filter_upwards with θ
    rw [schwartzTranslate_apply, sub_eq_add_neg]
  exact (e1.trans e2).trans e3.symm

/-! ## Brick 2 — the L² modulation operator `M_c`

The Fourier dual of translation is modulation: multiplication by the unit character `e^{i c ξ}`.
We build it on `L²(ℝ,ℂ)` directly — Mathlib has no bounded-function action on `Lp` — as the
foundation of the translate↔modulation intertwining `𝓕 ∘ τ_a = M_a ∘ 𝓕`. -/

/-- The unit Fourier character `ξ ↦ e^{i c ξ}` (modulus 1). -/
noncomputable def modChar (c ξ : ℝ) : ℂ := Complex.exp (Complex.I * (c * ξ : ℝ))

@[simp] theorem norm_modChar (c ξ : ℝ) : ‖modChar c ξ‖ = 1 := by
  rw [modChar, Complex.norm_exp]
  simp [Complex.mul_re]

theorem continuous_modChar (c : ℝ) : Continuous (modChar c) := by
  unfold modChar; fun_prop

/-- `e^{icξ}·g ∈ L²` whenever `g ∈ L²` (modulus-1 multiplier, via `MemLp.of_le_mul`). -/
theorem memLp_modChar_smul (c : ℝ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (fun ξ => modChar c ξ * (g : ℝ → ℂ) ξ) 2 volume := by
  refine MemLp.of_le_mul (c := 1) (Lp.memLp g)
    ((continuous_modChar c).aestronglyMeasurable.mul (Lp.aestronglyMeasurable g)) ?_
  filter_upwards with ξ
  simp

/-- **Wiener brick 2 — the L² modulation operator** `M_c : g ↦ (ξ ↦ e^{icξ} g(ξ))`. -/
noncomputable def modL2 (c : ℝ) (g : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_modChar_smul c g).toLp _

theorem coeFn_modL2 (c : ℝ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    (modL2 c g : ℝ → ℂ) =ᵐ[volume] fun ξ => modChar c ξ * (g : ℝ → ℂ) ξ :=
  (memLp_modChar_smul c g).coeFn_toLp

/-- `M_c` is additive (it is multiplication by a fixed function). -/
theorem modL2_add (c : ℝ) (g h : Lp ℂ 2 (volume : Measure ℝ)) :
    modL2 c (g + h) = modL2 c g + modL2 c h := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_modL2 c (g + h), coeFn_modL2 c g, coeFn_modL2 c h,
    Lp.coeFn_add g h, Lp.coeFn_add (modL2 c g) (modL2 c h)] with ξ h0 h1 h2 h3 h4
  rw [h0, h4, Pi.add_apply, h1, h2, h3, Pi.add_apply, mul_add]

/-- `M_c` is an `L²`-isometry: `‖M_c g‖ = ‖g‖` (the character has modulus 1). -/
theorem norm_modL2 (c : ℝ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖modL2 c g‖ = ‖g‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  refine (eLpNorm_congr_ae (coeFn_modL2 c g)).trans ?_
  refine eLpNorm_congr_norm_ae ?_
  filter_upwards with ξ
  rw [norm_mul, norm_modChar, one_mul]

/-! ## Brick 4 — the translate→modulation intertwining `𝓕 ∘ τ_a = M ∘ 𝓕`

The Fourier transform diagonalizes translation: it turns the rapidity boost (a translation) into
multiplication by the unit character.  We prove the pointwise Schwartz identity first, then lift it
to the `L²` Fourier unitary (`MeasureTheory.Lp.fourierTransformₗᵢ`, notation `𝓕`) by density. -/

open scoped RealInnerProductSpace FourierTransform

/-- **Wiener brick 4a — the Schwartz translate→modulation identity (pointwise).**
    `𝓕(f(·−a))(w) = e^{−2πi a w} · 𝓕f(w)` — the Fourier dual of translation is modulation by the
    unit character `modChar (−2πa)`.  Via `fourier_coe` (Schwartz `𝓕` = integral `𝓕` on the coeFn) and
    `VectorFourier.fourierIntegral_comp_add_right`. -/
theorem fourier_schwartzTranslate (a : ℝ) (f : 𝓢(ℝ, ℂ)) (w : ℝ) :
    (𝓕 (schwartzTranslate (-a) f)) w = modChar (-(2 * Real.pi * a)) w * (𝓕 f) w := by
  rw [fourier_coe, fourier_coe]
  have hcoe : (⇑(schwartzTranslate (-a) f) : ℝ → ℂ) = (⇑f) ∘ (fun v => v + (-a)) := by
    funext x; rw [Function.comp_apply, schwartzTranslate_apply]
  rw [hcoe]
  have key : (𝓕 ((⇑f) ∘ (fun v => v + (-a))) : ℝ → ℂ)
      = fun w => 𝐞 (innerₗ ℝ (-a) w) • (𝓕 (⇑f) : ℝ → ℂ) w :=
    VectorFourier.fourierIntegral_comp_add_right 𝐞 volume (innerₗ ℝ) (⇑f) (-a)
  rw [key]
  dsimp only
  have hchar : ((𝐞 (innerₗ ℝ (-a) w) : Circle) : ℂ) = modChar (-(2 * Real.pi * a)) w := by
    rw [Real.fourierChar_apply, modChar]
    congr 1
    have hinner : innerₗ ℝ (-a) w = -a * w := by
      rw [innerₗ_apply_apply]; exact Real.inner_apply (-a) w
    rw [hinner]; push_cast; ring
  rw [Circle.smul_def, hchar, smul_eq_mul]

/-- `M_c` is subtractive (companion to `modL2_add`), giving the isometry below. -/
theorem modL2_sub (c : ℝ) (g h : Lp ℂ 2 (volume : Measure ℝ)) :
    modL2 c (g - h) = modL2 c g - modL2 c h := by
  rw [Lp.ext_iff]
  filter_upwards [coeFn_modL2 c (g - h), coeFn_modL2 c g, coeFn_modL2 c h,
    Lp.coeFn_sub g h, Lp.coeFn_sub (modL2 c g) (modL2 c h)] with ξ h0 h1 h2 h3 h4
  rw [h0, h4, Pi.sub_apply, h1, h2, h3, Pi.sub_apply, mul_sub]

/-- `M_c` is an isometry of `L²` (modulus-1 multiplier), hence continuous. -/
theorem isometry_modL2 (c : ℝ) : Isometry (modL2 c) :=
  Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← modL2_sub, norm_modL2]

theorem continuous_modL2 (c : ℝ) : Continuous (modL2 c) := (isometry_modL2 c).continuous

/-- **Wiener brick 4b — the `L²` translate→modulation intertwining.**
    `𝓕 (boostUnitary a g) = M_{−2πa} (𝓕 g)` for *all* `g ∈ L²` — the boost (a translation) becomes
    multiplication by the unit character under the `L²` Fourier unitary.  Proven on the dense Schwartz
    range (brick 4a + `toLp_fourier_eq` + `boostUnitary_toLp`) and extended by `DenseRange.equalizer`
    (both sides continuous: `𝓕`/`boostUnitary` are isometry-equivs, `M_c` is `continuous_modL2`). -/
theorem fourierL2_boostUnitary (a : ℝ) (g : Lp ℂ 2 (volume : Measure ℝ)) :
    𝓕 (boostUnitary a g) = modL2 (-(2 * Real.pi * a)) (𝓕 g) := by
  have hF : Continuous (fun g : Lp ℂ 2 (volume : Measure ℝ) => 𝓕 (boostUnitary a g)) :=
    (Lp.fourierTransformₗᵢ ℝ ℂ).continuous.comp (boostUnitary a).continuous
  have hG : Continuous
      (fun g : Lp ℂ 2 (volume : Measure ℝ) => modL2 (-(2 * Real.pi * a)) (𝓕 g)) :=
    (continuous_modL2 _).comp (Lp.fourierTransformₗᵢ ℝ ℂ).continuous
  have base : (fun g : Lp ℂ 2 (volume : Measure ℝ) => 𝓕 (boostUnitary a g))
        ∘ (SchwartzMap.toLpCLM ℝ ℂ 2 volume)
      = (fun g : Lp ℂ 2 (volume : Measure ℝ) => modL2 (-(2 * Real.pi * a)) (𝓕 g))
        ∘ (SchwartzMap.toLpCLM ℝ ℂ 2 volume) := by
    funext f
    simp only [Function.comp_apply, toLpCLM_apply]
    rw [boostUnitary_toLp, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq, Lp.ext_iff]
    filter_upwards [(𝓕 (schwartzTranslate (-a) f)).coeFn_toLp 2,
      coeFn_modL2 (-(2 * Real.pi * a)) ((𝓕 f).toLp 2), (𝓕 f).coeFn_toLp 2] with ξ h1 h2 h3
    rw [h1, h2, h3, fourier_schwartzTranslate]
  exact congrFun (DenseRange.equalizer
    (denseRange_toLpCLM (F := ℂ) (p := 2) (by norm_num)) hF hG base) g

/-! ## Brick 5 — the Wiener bridge: boost-orbit inner product = integral Fourier transform -/

open scoped ComplexConjugate

/-- The unit character conjugates to its inverse: `conj (e^{icξ}) = e^{−icξ}`. -/
theorem conj_modChar (c ξ : ℝ) : conj (modChar c ξ) = modChar (-c) ξ := by
  rw [modChar, modChar, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- **Wiener brick 5 — the bridge.**  Via Plancherel (`inner_fourier_eq`) and the intertwining
    (brick 4), the boost-orbit inner product is the integral (inverse) Fourier transform of
    `k(ξ) = conj(𝓕g₀ ξ)·𝓕h ξ ∈ L¹`:
    `⟪boostUnitary a g₀, h⟫ = ∫ e^{+2πi a ξ}·conj(𝓕g₀ ξ)·𝓕h ξ dξ`.
    So the orbit-orthogonality condition `∀a, ⟪…⟫ = 0` becomes the vanishing of the FT of `k` — the
    exact hypothesis of the L¹ uniqueness theorem (next brick). -/
theorem inner_boostUnitary_eq_integral (a : ℝ) (g₀ h : Lp ℂ 2 (volume : Measure ℝ)) :
    inner ℂ (boostUnitary a g₀) h
      = ∫ ξ, modChar (2 * Real.pi * a) ξ
          * (conj ((𝓕 g₀ : Lp ℂ 2 (volume : Measure ℝ)) ξ)
              * (𝓕 h : Lp ℂ 2 (volume : Measure ℝ)) ξ) := by
  rw [← MeasureTheory.Lp.inner_fourier_eq, fourierL2_boostUnitary, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_modL2 (-(2 * Real.pi * a)) (𝓕 g₀)] with ξ hξ
  rw [hξ, RCLike.inner_apply', map_mul, conj_modChar, neg_neg]
  ring

/-! ## Brick 6 — Fourier injectivity on L¹ closes the Wiener argument

`k := conj(𝓕g₀)·𝓕h ∈ L¹`.  Brick 6a identifies its function Fourier transform with the boost-orbit
correlation, so the orbit-orthogonality hypothesis becomes `𝓕 k ≡ 0`; brick 6b (next) is the generic
L¹ uniqueness `Integrable k ∧ 𝓕 k = 0 ⟹ k =ᵐ 0`. -/

/-- **Wiener brick 6a — the reduction.**  The function Fourier transform of `k(ξ) = conj(𝓕g₀ ξ)·𝓕h ξ`
    at `w` equals the boost-orbit correlation `⟪boostUnitary (−w) g₀, h⟫` (brick 5 at `a = −w`, matching
    the `𝓕`-character `𝐞(−⟪ξ,w⟫) = modChar(2π(−w))ξ`).  Hence `(∀a, ⟪boost_a g₀,h⟫ = 0) ⟹ 𝓕 k ≡ 0`. -/
theorem fourier_correlation_eq (g₀ h : Lp ℂ 2 (volume : Measure ℝ)) (w : ℝ) :
    𝓕 (fun ξ => conj ((𝓕 g₀ : Lp ℂ 2 (volume : Measure ℝ)) ξ)
        * (𝓕 h : Lp ℂ 2 (volume : Measure ℝ)) ξ) w
      = inner ℂ (boostUnitary (-w) g₀) h := by
  rw [inner_boostUnitary_eq_integral, Real.fourier_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  dsimp only
  have hchar : ((𝐞 (-inner ℝ ξ w) : Circle) : ℂ) = modChar (2 * Real.pi * (-w)) ξ := by
    rw [Real.fourierChar_apply, modChar]
    congr 1
    rw [Real.inner_apply]; push_cast; ring
  rw [Circle.smul_def, hchar, smul_eq_mul]

/-- **Wiener brick 6b — Fourier injectivity on L¹.**  If `k ∈ L¹(ℝ)` and its (function) Fourier
    transform vanishes identically, then `k = 0` a.e.  Proof: it suffices (`AEEqOfIntegralContDiff`)
    that `∫ g·k = 0` for every real smooth compactly-supported test `g`; package its complexification
    `G:=↑∘g` as a Schwartz map, write `G = 𝓕(𝓕⁻G)` (Schwartz inversion) and apply the multiplication
    formula `∫ 𝓕(𝓕⁻G)·k = ∫ (𝓕⁻G)·𝓕k` (`integral_fourierIntegral_smul_eq_flip`, `innerₗ` symmetric)
    `= 0` since `𝓕 k = 0`. -/
theorem ae_eq_zero_of_fourier_eq_zero {k : ℝ → ℂ} (hk : Integrable k)
    (h : ∀ w, 𝓕 k w = 0) : k =ᵐ[volume] 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hk.locallyIntegrable
  intro g hg_smooth hg_supp
  have hGc_smooth := hg_smooth.continuousLinearMap_comp Complex.ofRealCLM
  have hGc_supp : HasCompactSupport (⇑Complex.ofRealCLM ∘ g) := hg_supp.comp_left (map_zero _)
  set G : 𝓢(ℝ, ℂ) := hGc_supp.toSchwartzMap hGc_smooth with hGdef
  have hGcoe : ∀ x, G x = (g x : ℂ) := fun x => Complex.ofRealCLM_apply (g x)
  set F : 𝓢(ℝ, ℂ) := 𝓕⁻ G with hFdef
  have hinv : 𝓕 F = G := FourierTransform.fourier_fourierInv_eq G
  have hfe : 𝓕 (⇑F) = (⇑G : ℝ → ℂ) := by rw [← fourier_coe, hinv]
  have hrw : (fun ξ => g ξ • k ξ) = fun ξ => 𝓕 (⇑F) ξ • k ξ := by
    funext ξ
    rw [hfe, hGcoe]
    simp [Complex.real_smul]
  rw [hrw,
    show (fun ξ => 𝓕 (⇑F) ξ • k ξ)
      = fun ξ => VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) (⇑F) ξ • k ξ from rfl,
    VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner F.integrable hk]
  have hz : ∀ x, VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ) k x = 0 := h
  simp only [flip_innerₗ, hz, smul_zero, integral_zero]

/-- **Wiener brick 7 — the Tauberian conclusion.**  If `𝓕 g₀ ≠ 0` a.e. and `h` is orthogonal to the
    entire boost orbit of `g₀`, then `h = 0`.  Chains 6a (orbit-orthogonality ⟹ `𝓕 k ≡ 0`, `k=conj(𝓕g₀)·𝓕h ∈ L¹`)
    with 6b (`𝓕 k = 0 ⟹ k=ᵐ0`); then `𝓕g₀≠0` a.e. forces `𝓕 h = 0` a.e. `⟹ 𝓕 h = 0 ⟹ h = 0` (`𝓕` an isometry). -/
theorem boost_orbit_total_of_fourier_ne_zero (g₀ h : Lp ℂ 2 (volume : Measure ℝ))
    (hg₀ : ∀ᵐ ξ ∂volume, (𝓕 g₀ : Lp ℂ 2 (volume : Measure ℝ)) ξ ≠ 0)
    (horth : ∀ a, inner ℂ (boostUnitary a g₀) h = 0) : h = 0 := by
  have hk0 : ∀ w, 𝓕 (fun ξ => (starRingEnd ℂ) ((𝓕 g₀ : Lp ℂ 2 (volume : Measure ℝ)) ξ)
      * (𝓕 h : Lp ℂ 2 (volume : Measure ℝ)) ξ) w = 0 := by
    intro w; rw [fourier_correlation_eq]; exact horth (-w)
  have hkInt : Integrable (fun ξ => (starRingEnd ℂ) ((𝓕 g₀ : Lp ℂ 2 (volume : Measure ℝ)) ξ)
      * (𝓕 h : Lp ℂ 2 (volume : Measure ℝ)) ξ) :=
    MemLp.integrable_mul (Lp.memLp (𝓕 g₀ : Lp ℂ 2 (volume : Measure ℝ))).star
      (Lp.memLp (𝓕 h : Lp ℂ 2 (volume : Measure ℝ)))
  have hkae := ae_eq_zero_of_fourier_eq_zero hkInt hk0
  have hFh0 : (⇑(𝓕 h : Lp ℂ 2 (volume : Measure ℝ))) =ᵐ[volume] 0 := by
    filter_upwards [hkae, hg₀] with ξ hk hg
    rcases mul_eq_zero.mp hk with h1 | h2
    · exact absurd (star_eq_zero.mp h1) hg
    · exact h2
  have hF0 : (𝓕 h : Lp ℂ 2 (volume : Measure ℝ)) = 0 :=
    Lp.eq_zero_iff_ae_eq_zero.mpr hFh0
  exact (Lp.fourierTransformₗᵢ ℝ ℂ).injective (hF0.trans (map_zero _).symm)

/-- **Wiener brick 8c — a nonzero real-analytic function is `≠ 0` a.e.**  The zero set of a function
    analytic on all of `ℝ` (and not identically zero) is co-discrete, hence Lebesgue-null
    (`AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected` + `ae_restrict_le_codiscreteWithin`).
    This is the final step turning "the boost-orbit generator's Fourier transform is entire and `≢ 0`"
    into the Wiener hypothesis `𝓕 g₀ ≠ 0` a.e. of brick 7. -/
theorem ae_ne_zero_of_analyticOnNhd {F : ℝ → ℂ} (hF : AnalyticOnNhd ℝ F Set.univ)
    (hF0 : ∃ x, F x ≠ 0) : ∀ᵐ x ∂(volume : Measure ℝ), F x ≠ 0 := by
  rcases hF.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with h | h
  · obtain ⟨x, hx⟩ := hF0
    have hzero := h (Set.mem_univ x)
    simp only [Pi.zero_apply] at hzero
    exact absurd hzero hx
  · have hle := ae_restrict_le_codiscreteWithin (μ := (volume : Measure ℝ)) MeasurableSet.univ
    rw [Measure.restrict_univ] at hle
    exact hle h

/-- **Wiener brick 8c′ — an entire function nonzero somewhere on `ℝ` is `≠ 0` a.e. on `ℝ`.**
    The restriction of an entire `F : ℂ → ℂ` to the real axis is real-analytic
    (`analyticOnNhd_univ_iff_differentiable` + `AnalyticAt.restrictScalars`/`.comp` with `ofRealCLM`),
    so brick 8c applies.  This is the exact shape consumed by brick 8: the Fourier transform of the
    super-exponentially-decaying wedge amplitude `Krep m f₀` extends to an entire function. -/
theorem ae_ne_zero_of_differentiable {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hF0 : ∃ x : ℝ, F (Complex.ofReal x) ≠ 0) :
    ∀ᵐ x ∂(volume : Measure ℝ), F (Complex.ofReal x) ≠ 0 := by
  have hana : AnalyticOnNhd ℝ (fun x : ℝ => F (Complex.ofReal x)) Set.univ := by
    intro x _
    have hC : AnalyticAt ℂ F (x : ℂ) :=
      (hF.differentiableOn.analyticOnNhd isOpen_univ) (x : ℂ) (Set.mem_univ _)
    have hR : AnalyticAt ℝ F (x : ℂ) := hC.restrictScalars
    have ho : AnalyticAt ℝ (fun t : ℝ => (t : ℂ)) x := Complex.ofRealCLM.analyticAt x
    exact hR.comp ho
  exact ae_ne_zero_of_analyticOnNhd hana hF0

/-- **Wiener brick 8a-foundation — `exp(−b|x|)` is integrable on `ℝ`** for `b > 0`.  The reusable both-ends
    exponential building block: `f =O[atBot] exp(b·)` and `f =O[atTop] exp(−b·)`, each integrable at its end
    (`exp_neg_integrableOn_Ioi` + reflection), via `LocallyIntegrable.integrable_of_isBigO_atBot_atTop`.
    Dominates the `1/cosh²θ` decay of `Krep`, giving `Krep ∈ L¹` and its finite exponential moments. -/
theorem integrable_exp_neg_mul_abs {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => Real.exp (-b * |x|)) := by
  have hcont : Continuous (fun x : ℝ => Real.exp (-b * |x|)) := by fun_prop
  have hbot : IntegrableOn (fun x : ℝ => Real.exp (b * x)) (Set.Iio 0) := by
    have hpre : Neg.neg ⁻¹' (Set.Ioi (0 : ℝ)) = Set.Iio 0 := by ext x; simp
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      measurableEmbedding_neg (f := fun x : ℝ => Real.exp (-b * x)) (s := Set.Ioi 0)
    rw [hpre] at h
    refine (h.mpr (exp_neg_integrableOn_Ioi 0 hb)).congr_fun ?_ measurableSet_Iio
    intro x _; simp only [Function.comp_apply]; congr 1; ring
  refine hcont.locallyIntegrable.integrable_of_isBigO_atBot_atTop
    (g := fun x => Real.exp (b * x)) ?_ ⟨Set.Iio 0, Filter.Iio_mem_atBot 0, hbot⟩
    (g' := fun x => Real.exp (-b * x)) ?_ ⟨Set.Ioi 0, Filter.Ioi_mem_atTop 0, exp_neg_integrableOn_Ioi 0 hb⟩
  · refine (Filter.EventuallyEq.isBigO ?_)
    filter_upwards [Filter.eventually_lt_atBot 0] with x hx
    rw [abs_of_neg hx]; congr 1; ring
  · refine (Filter.EventuallyEq.isBigO ?_)
    filter_upwards [Filter.eventually_gt_atTop 0] with x hx
    rw [abs_of_pos hx]

/-- **`|θ|·exp(−d|θ|)` is integrable on `ℝ`** for `d > 0` — the derivative-domination building block for the
    FT-holomorphy (8b): `|θ| ≤ (2/d)·exp((d/2)|θ|)` (from `t ≤ exp t`) absorbs the `|θ|` into a slower exponential
    dominated by `integrable_exp_neg_mul_abs (d/2)`. -/
theorem integrable_abs_mul_exp_neg_mul_abs {d : ℝ} (hd : 0 < d) :
    Integrable (fun θ : ℝ => |θ| * Real.exp (-d * |θ|)) := by
  refine ((integrable_exp_neg_mul_abs (show (0 : ℝ) < d / 2 by linarith)).const_mul (2 / d)).mono'
    (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards with θ
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hb : d / 2 * |θ| ≤ Real.exp (d / 2 * |θ|) := by
    have := Real.add_one_le_exp (d / 2 * |θ|); linarith
  have h1 : |θ| ≤ 2 / d * Real.exp (d / 2 * |θ|) := by
    have key := mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ 2 / d by positivity)
    rwa [show 2 / d * (d / 2 * |θ|) = |θ| by field_simp] at key
  have hexpprod : Real.exp (d / 2 * |θ|) * Real.exp (-d * |θ|) = Real.exp (-(d / 2) * |θ|) := by
    rw [← Real.exp_add]; congr 1; ring
  calc |θ| * Real.exp (-d * |θ|)
      ≤ 2 / d * Real.exp (d / 2 * |θ|) * Real.exp (-d * |θ|) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
    _ = 2 / d * Real.exp (-(d / 2) * |θ|) := by rw [mul_assoc, hexpprod]

/-- `(cosh θ)⁻² ≤ 4·exp(−2|θ|)` — from `exp|θ| ≤ 2cosh θ` (one of `e^{±θ}` equals `e^{|θ|}`). -/
theorem inv_cosh_sq_le_exp (θ : ℝ) : (Real.cosh θ ^ 2)⁻¹ ≤ 4 * Real.exp (-2 * |θ|) := by
  have hexp : Real.exp |θ| ≤ 2 * Real.cosh θ := by
    rw [Real.cosh_eq]
    rcases le_total 0 θ with h | h
    · rw [abs_of_nonneg h]; have := (Real.exp_pos (-θ)).le; linarith
    · rw [abs_of_nonpos h]; have := (Real.exp_pos θ).le; linarith
  have hexp2 : Real.exp (2 * |θ|) ≤ 4 * Real.cosh θ ^ 2 := by
    have h := mul_le_mul hexp hexp (Real.exp_nonneg _) (by positivity)
    calc Real.exp (2 * |θ|) = Real.exp |θ| * Real.exp |θ| := by rw [← Real.exp_add]; ring_nf
      _ ≤ 2 * Real.cosh θ * (2 * Real.cosh θ) := h
      _ = 4 * Real.cosh θ ^ 2 := by ring
  have hee : Real.exp (-2 * |θ|) * Real.exp (2 * |θ|) = 1 := by rw [← Real.exp_add]; simp
  rw [show (Real.cosh θ ^ 2)⁻¹ = 1 / Real.cosh θ ^ 2 by rw [one_div],
    div_le_iff₀ (by positivity)]
  nlinarith [hexp2, Real.exp_pos (-2 * |θ|), Real.exp_pos (2 * |θ|), hee]

/-- **Wiener brick 8a — `Krep m f ∈ L¹(ℝ)`** for a Schwartz test `f`: the localized rapidity amplitude is
    integrable, since `‖Krep m f θ‖ ≤ C·(cosh θ)⁻²` (`schwartz_Krep_decay_sq`) `≤ 4C·exp(−2|θ|)`, dominated by
    the integrable `exp(−2|θ|)` (`integrable_exp_neg_mul_abs`).  Makes the function Fourier transform of `Krep`
    well-defined and is the base for the L²↔L¹ agreement and the FT-holomorphy (8b). -/
theorem integrable_Krep (f : SchwartzMap V ℂ) {m : ℝ} (hm : m ≠ 0) :
    Integrable (Krep m (⇑f)) volume := by
  set C : ℝ := 16 * Real.pi ^ 2 * ((∫ v, ‖(⇑f) v‖) + (∫ v, ‖iteratedFDeriv ℝ 1 (⇑f) v‖)
      + (∫ v, ‖iteratedFDeriv ℝ 2 (⇑f) v‖)) / (Real.sqrt 2 * m ^ 2) with hCdef
  have hCnn : 0 ≤ C := by rw [hCdef]; positivity
  refine Integrable.mono' (g := fun θ => C * 4 * Real.exp (-2 * |θ|))
    ((integrable_exp_neg_mul_abs (by norm_num : (0 : ℝ) < 2)).const_mul (C * 4)) ?_ ?_
  · exact (Krep_continuous f.integrable).aestronglyMeasurable
  · filter_upwards with θ
    calc ‖Krep m (⇑f) θ‖ ≤ C * (Real.cosh θ ^ 2)⁻¹ := schwartz_Krep_decay_sq f hm θ
      _ ≤ C * (4 * Real.exp (-2 * |θ|)) := by gcongr; exact inv_cosh_sq_le_exp θ
      _ = C * 4 * Real.exp (-2 * |θ|) := by ring

end QIQTH.Fock.WienerL2
