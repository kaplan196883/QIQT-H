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

namespace QIQTH.Fock.WienerL2

open SchwartzMap

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

end QIQTH.Fock.WienerL2
