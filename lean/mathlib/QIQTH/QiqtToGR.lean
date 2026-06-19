import QIQTH.ClausiusToPernull
import QIQTH.DifferentialAreaLaw

/-!
# Assembling QIQT-H + Bekenstein ⇒ GR: the per-null tensor premise from the DERIVED modular relation

`DifferentialAreaLaw.differential_area_law` DERIVES the modular first-law relation `δ⟨K⟩ = η δA`
(`k' = η·a'`) from QIQT-H's own capacity bound + saturation + Klein positivity.  This file turns that
relation, per null direction `v`, into Jacobson's **pointwise** per-null premise
`BL(a·T − Ric) v = 0` — the exact hypothesis `pernull` that `jacobson_einstein_equation_of_state`
consumes — using only two clearly-labelled CITED inputs (Mathlib has no AQFT/Lorentzian-GR):

* `hFlux`  — Bisognano–Wichmann + boost heat flux: `δ⟨K⟩ = (2π/ℏ)·BL(T) v`  (the modular energy is the
  boost-energy flux `T_kk`);
* `hFocus` — Raychaudhuri (leading order): the area first-variation rate `a' = BL(Ric) v` (the focusing
  scalar `R_kk`).

The modular relation `hModular` is DERIVED from QIQT-H; only `hFlux`/`hFocus` are cited, and they are kept
SEPARATE from each other and from the area law — neither presupposes Einstein.  This isolates the *exact*
physics surface (the Type III₁ wedge-modular identification + Raychaudhuri focusing) that cannot be
Lean-proved, while everything QIQT-H supplies is derived.
-/

namespace QIQTH.QiqtToGR

open QIQTH.EinsteinEOS QIQTH.Curvature QIQTH.DifferentialAreaLaw
open Filter Topology

/-- **The pointwise per-null premise from the derived modular relation + cited AQFT/geometry.**
    From `δ⟨K⟩ = η δA` (`hModular`, DERIVED) together with the cited boost-flux (`hFlux`,
    Bisognano–Wichmann) and Raychaudhuri focusing (`hFocus`), with `a = 2π/(ℏη)`, the heat tensor
    `a·T − Ric` vanishes on the null vector `v`: `BL(a·T − Ric) v = 0`.  This is exactly Jacobson's
    `pernull` premise for the direction `v`. -/
theorem bl_pernull_of_modular (T Ric : Fin 4 → Fin 4 → ℝ) (v : Fin 4 → ℝ)
    {k' a' η hbar a : ℝ}
    (hbar0 : hbar ≠ 0) (heta : η ≠ 0) (ha : a = 2 * Real.pi / (hbar * η))
    (hModular : k' = η * a')
    (hFlux : k' = 2 * Real.pi / hbar * BL T v)
    (hFocus : a' = BL Ric v) :
    BL (fun i j => a * T i j - Ric i j) v = 0 := by
  have h1 : η * a' = 2 * Real.pi / hbar * BL T v := hModular.symm.trans hFlux
  have hkey : a * BL T v = BL Ric v := by
    rw [ha, ← hFocus]
    have key : 2 * Real.pi / (hbar * η) * BL T v = η⁻¹ * (2 * Real.pi / hbar * BL T v) := by
      field_simp
    rw [key, ← h1, ← mul_assoc, inv_mul_cancel₀ heta, one_mul]
  rw [BL_smul_sub a T Ric v, hkey, sub_self]

/-- **The per-null premise DERIVED from QIQT-H content + the two cited inputs.**  Composes
    `differential_area_law_of_relEntropy` (QIQT-H ⇒ `δ⟨K⟩ = η δA`) with `bl_pernull_of_modular`, so the
    only non-derived inputs are the labelled cited physics (`hFlux`, `hFocus`).

    QIQT-H content (along the deformation path `t` at this point/null direction):
    * `hbound` — the capacity **bound** `S ≤ η·A` (QIQT-H's `shannon_le_log_card`);
    * `hsat`   — saturation at the reference `S 0 = η·A 0` (`shannon_uniform_eq_log_card`);
    * `hDnn`,`hD0` — relative-entropy positivity `KE − S ≥ 0`, `= 0` at the reference (Klein,
      `relEntropy_nonneg`);
    * differentiability of `S, KE, A`.
    Cited (Mathlib-unprovable, kept SEPARATE): `hFlux` (Bisognano–Wichmann boost flux), `hFocus`
    (Raychaudhuri focusing).

    Conclusion: `BL(a·T − Ric) v = 0` — Jacobson's per-null premise.  No hypothesis is the area law or
    `BL(a·T − Ric) v = 0` itself; the area law is *derived* from the bound + saturation + Klein. -/
theorem bl_pernull_of_qiqt (T Ric : Fin 4 → Fin 4 → ℝ) (v : Fin 4 → ℝ)
    {S KE A : ℝ → ℝ} {s' k' a' η hbar a : ℝ}
    (hbar0 : hbar ≠ 0) (heta : η ≠ 0) (ha : a = 2 * Real.pi / (hbar * η))
    (hS : HasDerivAt S s' 0) (hK : HasDerivAt KE k' 0) (hA : HasDerivAt A a' 0)
    (hbound : ∀ᶠ t in 𝓝 0, S t ≤ η * A t) (hsat : S 0 = η * A 0)
    (hDnn : ∀ t, 0 ≤ KE t - S t) (hD0 : KE 0 - S 0 = 0)
    (hFlux : k' = 2 * Real.pi / hbar * BL T v)
    (hFocus : a' = BL Ric v) :
    BL (fun i j => a * T i j - Ric i j) v = 0 :=
  bl_pernull_of_modular T Ric v hbar0 heta ha
    (differential_area_law_of_relEntropy hS hK hA hbound hsat hDnn hD0).2 hFlux hFocus

end QIQTH.QiqtToGR
