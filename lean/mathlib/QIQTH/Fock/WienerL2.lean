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
import QIQTH.Fock.OneParticleBW

namespace QIQTH.Fock.WienerL2

open SchwartzMap MeasureTheory QIQTH.Fock.OneParticle QIQTH.Fock.OneParticleBW

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

end QIQTH.Fock.WienerL2
