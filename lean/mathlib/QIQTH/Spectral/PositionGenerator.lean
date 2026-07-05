/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The position operator `X` as a self-adjoint unbounded operator (Stone generator of `M_s = e^{isX}`)

Applying the **general Stone generator** (`QIQTH/Spectral/Stone.lean`) to the modulation group
`M_s = modulationLp s` on `L²(ℝ)` (the C₀ unitary group `e^{isX}`, `(M_s f)(x) = e^{isx} f(x)`): its Stone
hypotheses — the group law (`modulationLp_add`), `M_0 = 1` (`modulationLp_zero`), inner-product preservation
(`M_s` a ℂ-linear isometry, `modulationUnitary`), the isometry norm bound (`norm_modulationLp`), and strong
continuity (`continuous_modulationLp`) — are all in hand (`QIQTH/Spectral/ModulationFlow.lean`). So the
**position operator** `X := stoneGen modulationLp = −i d/ds M_s = x·` is a genuine *self-adjoint* unbounded
operator (`LinearPMap`) on `L²(ℝ)`.

This completes the canonical CCR operator pair `(P, X)` at the self-adjoint-generator level: `P = momentumOp`
(`QIQTH/Spectral/MomentumGenerator.lean`) is the generator of the translation group `e^{itP}`, and `X` is its
Fourier-dual twin, the generator of the modulation group `e^{isX}`. Together they realize the Weyl CCR
(`weyl_relation`). Axiom-free.

**Honest scope:** this is a spectral-theory capstone — COSMETIC for QG, not a QG advance. It is the mechanical
mirror of the momentum file; the mathematics is identical to the (closed) momentum case.

The `Lp`-elaboration friction (the `whnf`/`isDefEq` divergence on the `(stoneGen _).domain` projection through
the heavy `Lp`/`InnerProductSpace` instance tower) is handled by the same pattern as momentum:
`attribute [local irreducible] stoneGen stoneDomain` + explicit ambient `(H := Lp ℂ 2 volume)`.
-/
import QIQTH.Spectral.ModulationFlow
import QIQTH.Spectral.Stone
import QIQTH.Spectral.Garding

namespace QIQTH.Spectral.Multiplication

open MeasureTheory QIQTH.Spectral

/-- **The one-parameter group law** `M_{s+t} = M_s ∘L M_t` (Stone `hgrp`), from `modulationLp_add` reoriented. -/
theorem modulationLp_group (s t : ℝ) :
    (modulationLp (s + t) : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))
      = modulationLp s ∘L modulationLp t :=
  (modulationLp_add s t).symm

/-- Inner-product preservation: `⟪M_t a, M_t b⟫ = ⟪a, b⟫` (`M_t` a ℂ-linear isometry). The Stone hypothesis
    `hUinner` for the modulation group, via the unitary `modulationUnitary`. -/
theorem modulationLp_inner (t : ℝ) (a b : Lp ℂ 2 (volume : Measure ℝ)) :
    (inner ℂ (modulationLp t a) (modulationLp t b) : ℂ) = inner ℂ a b :=
  (modulationUnitary t).inner_map_map a b

/-- `‖M_t y‖ ≤ ‖y‖` — the contraction (in fact isometry) bound (`hUbd`) for the modulation group. -/
theorem modulationLp_norm_le (t : ℝ) (y : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖modulationLp t y‖ ≤ ‖y‖ :=
  (norm_modulationLp t y).le

attribute [local irreducible] QIQTH.Spectral.stoneGen QIQTH.Spectral.stoneDomain

/-- **★ The position operator `X`** = the (densely-definable) generator `−i d/ds M_s = x·` of the modulation
    group, as a `LinearPMap` on `L²(ℝ)`. -/
noncomputable def positionOp :
    Lp ℂ 2 (volume : Measure ℝ) →ₗ.[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  stoneGen modulationLp

/-- **★★★ The position operator `X` is self-adjoint:** `IsSelfAdjoint (stoneGen modulationLp)`. The generic
    `stoneGen_isSelfAdjoint` instantiated for the modulation group `M_s = e^{isX}` (group law
    `modulationLp_group`, `M_0 = 1` `modulationLp_zero`, unitarity `modulationLp_inner`, the isometry
    `modulationLp_norm_le`, strong continuity `continuous_modulationLp`). So `X = x·` is a genuine self-adjoint
    unbounded operator — the Fourier-dual twin of `momentumOp = P = −i d/dx`, completing the canonical CCR pair
    `(P, X)` at the self-adjoint-generator level. Cosmetic-for-QG spectral capstone. -/
theorem positionOp_isSelfAdjoint : IsSelfAdjoint (stoneGen modulationLp) :=
  stoneGen_isSelfAdjoint (H := Lp ℂ 2 (volume : Measure ℝ)) modulationLp
    modulationLp_group modulationLp_zero modulationLp_inner
    modulationLp_norm_le continuous_modulationLp

end QIQTH.Spectral.Multiplication
