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

end QIQTH.Fock.WienerL2
