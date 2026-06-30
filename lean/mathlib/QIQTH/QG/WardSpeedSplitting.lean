/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# J3 — the Ward dichotomy for the radiative speed splitting (CPSUV escape ⟺ B = 0)

Phase of `COVARIANT_CAPACITY_CPSUV_PLAN.md` (J3). The decisive structural fact behind the CPSUV question
(GPT-5.5-pro consult): the one-loop matter two-point function `Γ⁽²⁾(p)` has a temporal kinetic coefficient `Z_t`
(the coefficient of `p₀²`) and a spatial one `Z_s` (the coefficient of `|p|²`), and the speed splitting is

    Δc² = Z_s / Z_t − 1.

A **Lorentz-scalar** regulator gives the Ward identity `Γ⁽²⁾(p) = F(p²)` ⟹ `Z_t = Z_s` ⟹ `Δc² = 0`. A
**frame-picking** regulator (a fixed diamond / preferred timelike `u`) allows `Γ⁽²⁾(p) = A·p² + B·(u·p)²`, whose
`(u·p)²` term adds **only** to the temporal coefficient (`(u·p)² = p₀²` in `u`'s rest frame), giving `Z_t = A + B`,
`Z_s = A`, so `Δc² = −B/(A+B)`. Hence the entire CPSUV-escape question collapses to a single scalar condition:

    Δc² = 0  ⟺  Z_t = Z_s  ⟺  the anisotropy coefficient  B = 0.

This file proves that dichotomy as an axiom-free algebraic theorem — the machine-checked interface that reduces
"does QIQT-H's covariant capacity escape CPSUV" to "is its matter-loop regulator Lorentz-scalar (B = 0)". (J1
showed numerically that `B` is sourced by the regulator's frame anisotropy `A_F = ⟨k₄²−k_x²⟩_F`; J2 showed
QIQT-H's capacity is an algebraic record-count with no matter-field symbol, so `B` is set by the *separately
supplied* matter UV kernel — J6.) Axiom-free (standard `propext`/`Classical.choice`/`Quot.sound`).
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace QIQTH.QG

/-- **The radiative speed splitting** `Δc² = Z_s/Z_t − 1` of a matter two-point function with temporal kinetic
coefficient `Zt` (coefficient of `p₀²`) and spatial coefficient `Zs` (coefficient of `|p|²`). -/
noncomputable def speedSplitting (Zt Zs : ℝ) : ℝ := Zs / Zt - 1

/-- **Isotropy ⟹ no splitting.** If the two-point function is isotropic (`Zt = Zs`, the Lorentz-scalar Ward
identity `Γ⁽²⁾ = F(p²)`), the speed splitting vanishes. -/
theorem speedSplitting_eq_zero_of_isotropic {Zt Zs : ℝ} (hZt : Zt ≠ 0) (h : Zt = Zs) :
    speedSplitting Zt Zs = 0 := by
  rw [speedSplitting, ← h, div_self hZt, sub_self]

/-- **The dichotomy: `Δc² = 0 ⟺ isotropic`.** For `Zt ≠ 0`, the speed splitting vanishes iff `Zt = Zs`. -/
theorem speedSplitting_eq_zero_iff {Zt Zs : ℝ} (hZt : Zt ≠ 0) :
    speedSplitting Zt Zs = 0 ↔ Zt = Zs := by
  rw [speedSplitting, sub_eq_zero, div_eq_one_iff_eq hZt, eq_comm]

/-- The kinetic coefficients of the anisotropic form `Γ⁽²⁾(p) = A·p² + B·(u·p)²` (with `u` the preferred time
direction) are `Z_t = A + B` and `Z_s = A`; the splitting is `Δc² = −B/(A+B)`. -/
theorem speedSplitting_aniso (A B : ℝ) (hAB : A + B ≠ 0) :
    speedSplitting (A + B) A = -B / (A + B) := by
  rw [speedSplitting]
  field_simp
  ring

/-- **★ J3 — the escape criterion.** For the anisotropic two-point form `Γ⁽²⁾ = A·p² + B·(u·p)²` (`A + B ≠ 0`),
the radiative speed splitting **vanishes iff the anisotropy coefficient `B = 0`**:

    Δc² = 0  ⟺  B = 0.

So "does the regulator escape CPSUV" reduces to the single scalar condition `B = 0` — i.e. the matter-loop
regulator carries **no preferred-`u` (Lorentz-violating) term**, equivalently has a Lorentz-scalar symbol. -/
theorem speedSplitting_aniso_eq_zero_iff (A B : ℝ) (hAB : A + B ≠ 0) :
    speedSplitting (A + B) A = 0 ↔ B = 0 := by
  rw [speedSplitting_eq_zero_iff hAB]
  constructor
  · intro h; linarith
  · intro h; rw [h, add_zero]

/-- **Nonzero anisotropy ⟹ CPSUV.** Contrapositive packaging: if `B ≠ 0` (a frame-picking regulator), the speed
splitting is nonzero — radiative Lorentz violation fires. -/
theorem speedSplitting_aniso_ne_zero_of_B_ne_zero (A B : ℝ) (hAB : A + B ≠ 0) (hB : B ≠ 0) :
    speedSplitting (A + B) A ≠ 0 := by
  rw [Ne, speedSplitting_aniso_eq_zero_iff A B hAB]
  exact hB

end QIQTH.QG
