/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# Scope firewall — the induced-`G` package predicts NO numerical value of `G` without an external scale

The induced-gravity relation `1/G = N·Λ_s²` (`QIQTH.InducedG.inducedG`, `G` delivered as an OUTPUT of the
species count `N` and the granularity scale `Λ_s`) is an exact axiom-free identity.  This file makes the
*honesty* of that claim a THEOREM, not just a docstring caveat: the relation on its own does NOT fix the
numerical value of `G`.

- **`inducedG_rescale_degeneracy`**: `G` depends only on the single combination `N·Λ²` — rescaling
  `N ↦ N/q²`, `Λ ↦ q·Λ` leaves `G` invariant.  Neither `N` nor `Λ` is separately pinned.
- **`any_positive_G_realizable`**: for ANY `N>0` and ANY target `G>0` there is a scale `Λ>0` with
  `inducedG N Λ = G` — every positive value of `G` is realizable, so the mechanism alone predicts none.

Together these are a machine-checked SCOPE FIREWALL: the numerical value of `G` requires the external input
`Λ_s` (and the species accounting `N`); it is NOT an output of the finite-capacity mechanism by itself.
This guards the manuscript against the overclaim "we derive the value of Newton's constant" — what is proven
is "given `N` and `Λ_s`, the model outputs `1/G = N·Λ_s²`", and the value of `G` is not predicted without
those inputs.  Mirrors the existing vacuity/rigidity guards (`dyadic_covariance_insufficient`,
`bulk_entropy_volume_law`): a negative theorem that makes a load-bearing assumption visible.  Axiom-free.
-/
import Mathlib
import QIQTH.InducedNewtonConstant

namespace QIQTH.ScopeAudit

open QIQTH.InducedG

/-- **Scale degeneracy of the induced `G`.**  Rescaling the species count `N ↦ N/q²` and the granularity
    scale `Λ ↦ q·Λ` leaves the induced `G` UNCHANGED: `inducedG (N/q²) (q·Λ) = inducedG N Λ`.  So `G` is a
    function of the single combination `N·Λ²` only; neither `N` nor `Λ` is separately determined by the
    relation.  (The dimensionless content is `G/a₀² = 1/N`; the scale must come from outside.) -/
theorem inducedG_rescale_degeneracy (N Λ q : ℝ) (hN : N ≠ 0) (hΛ : Λ ≠ 0) (hq : q ≠ 0) :
    inducedG (N / q ^ 2) (q * Λ) = inducedG N Λ := by
  unfold inducedG
  field_simp

/-- **Non-identifiability — the scope firewall.**  For ANY species count `N > 0` and ANY target value
    `G > 0`, there exists a granularity scale `Λ > 0` making `inducedG N Λ = G`.  Hence the relation
    `1/G = N·Λ²` predicts NO numerical value of `G` on its own: every positive `G` is realizable by a
    suitable choice of the external scale `Λ` (`= Λ_s`).  The value of `G` requires the external input `Λ_s`
    (plus the species accounting `N`); it is NOT an output of the mechanism alone. -/
theorem any_positive_G_realizable (N G : ℝ) (hN : 0 < N) (hG : 0 < G) :
    ∃ Λ > 0, inducedG N Λ = G := by
  refine ⟨Real.sqrt (1 / (N * G)), Real.sqrt_pos.mpr (by positivity), ?_⟩
  unfold inducedG
  rw [Real.sq_sqrt (by positivity)]
  field_simp

end QIQTH.ScopeAudit
