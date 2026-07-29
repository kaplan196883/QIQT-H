/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# RadialRicciUnconditional — the first-derivative radial van-Vleck −Ric form, UNCONDITIONAL near the RNC centre

The van-Vleck radial FIRST-derivative identity on the real exp-differential
(`QIQTH.JacobianRegularity.expJacobianDet_radialDeriv_real`, the 1st-order sibling of the
`(b)`-side van-Vleck −Ric closer) reads
```
  ∃ Bd, HasDerivAt (fun s => s • D(exp_p)_{s•v}) Bd 1 ∧
    radialDeriv (fun x => log J(x)) v = tr(Bd · (D exp_p)_v⁻¹) − n,
```
where `J = expJacobianDet` is the exp-map Jacobian determinant and `θ_B := tr(Bd·(D exp_p)_v⁻¹)`
the Raychaudhuri expansion.  As stated there it is CONDITIONAL on the two carried no-conjugate-point
positivity hypotheses

* `hJv : 0 < J v`               (no conjugate point AT `v`), and
* `hpos : ∀ᶠ s in 𝓝 1, 0 < J(s • v)`   (no conjugate point along the ray, near `s = 1`),

plus the domain hypothesis `hv : ‖v‖ < expRho` and the top-level metric regularity `hC`.

This file DISCHARGES both `hJv` and `hpos` (and `hv`) near the RNC centre.  The exp-Jacobian
determinant is continuous at `0` with `J(0) = 1 > 0`, so `J > 0` on a neighbourhood of `0`
(`QIQTH.JacobianRadial.expJacobianDet_pos_nhds`).  Consequently:

* for `v` near `0`, `∀ᶠ x in 𝓝 v, 0 < J x` (via `eventually_eventually_nhds`), which supplies both
  `hJv` (the value at `v`) and — by continuity of the ray `s ↦ s • v` — `hpos` (the values along
  the ray for `s` near `1`);
* the exp-ball `‖v‖ < expRho` is a neighbourhood of `0`, supplying `hv`.

The result is the SAME first-derivative radial van-Vleck −Ric conclusion with the no-conjugate
positivity data `hJv`/`hpos` fully removed, for `v` in a neighbourhood of the centre — exactly the
near-centre regime the parametrix / `a₁` argument uses.

## Honest scope

* This is the FIRST-DERIVATIVE (Euler) radial identity, the 1st-order sibling of the `(b)`-side
  van-Vleck −Ric closer.  The ONLY hypothesis that remains is the top-level metric regularity `hC`
  (`christoffel` is `C^∞`), a genuine non-vacuous input, NOT a no-conjugate hypothesis.
* The domain is HONEST: `∀ᶠ v in 𝓝 0`, i.e. a neighbourhood of the RNC centre only.  Nothing is
  claimed for `v` away from the centre (where conjugate points may occur).
* This does NOT prove the deep matrix Jacobi identity `B'' = −R̃ B`, and it is UNRELATED to the
  heat-kernel coefficient `a₁ = R/6` (M6) and the M5 continuum step.

Axiom-free (`propext`, `Classical.choice`, `Quot.sound` only).
-/
import Mathlib
import QIQTH.JacobiDerivReal
import QIQTH.JacobianRadial

namespace QIQTH.JacobianRegularity

open QIQTH.Curvature QIQTH.ExpMap QIQTH.Geodesic QIQTH.PullbackMetric QIQTH.RadialDistance
open Finset Matrix
open scoped Topology

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **The no-conjugate positivity along the ray, from positivity on a neighbourhood of `v`.**

If `J = expJacobianDet` is positive on a whole neighbourhood of `v`, then it is positive along the
ray `s ↦ s • v` for `s` near `1` — the exact `hpos` shape required by
`expJacobianDet_radialDeriv_real`.  The ray `s ↦ s • v` is continuous with value `v` at `s = 1`, so
it pulls the neighbourhood-of-`v` positivity back to a `𝓝 1` eventually-statement.

This is the standalone "positivity ⟹ no-conjugate along the ray" feed. -/
theorem expJacobianDet_pos_ray_of_pos_nhds (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (hVnhd : ∀ᶠ x in 𝓝 v, 0 < QIQTH.JacobianDet.expJacobianDet g gi hC p x) :
    ∀ᶠ s in nhds (1 : ℝ), 0 < QIQTH.JacobianDet.expJacobianDet g gi hC p (s • v) := by
  have hcont : Filter.Tendsto (fun s : ℝ => s • v) (𝓝 (1 : ℝ)) (𝓝 v) := by
    have h : Filter.Tendsto (fun s : ℝ => s • v) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) • v)) :=
      (continuous_id.smul continuous_const).tendsto (1 : ℝ)
    simpa only [one_smul] using h
  exact hcont.eventually hVnhd

/-- **The van-Vleck radial FIRST-derivative −Ric identity, UNCONDITIONAL near the RNC centre.**

For `v` in a neighbourhood of the centre `0`, the carried no-conjugate positivity data of
`expJacobianDet_radialDeriv_real` (`hJv : 0 < J v` and `hpos : ∀ᶠ s in 𝓝 1, 0 < J(s•v)`) and the
domain hypothesis `hv : ‖v‖ < expRho` are all DISCHARGED, and the same first-derivative radial
van-Vleck conclusion holds:
```
  ∃ Bd, HasDerivAt (fun s => s • D(exp_p)_{s•v}) Bd 1 ∧
    radialDeriv (fun x => log J(x)) v = tr(Bd · (D exp_p)_v⁻¹) − n.
```

Discharge: `J` is continuous at `0` with `J(0) = 1 > 0`, so `J > 0` on a neighbourhood of `0`
(`expJacobianDet_pos_nhds`); by `eventually_eventually_nhds` this gives, for `v` near `0`,
positivity on a neighbourhood of `v`, which supplies `hJv` (value at `v`) and `hpos` (along the ray,
`expJacobianDet_pos_ray_of_pos_nhds`).  The exp-ball is a neighbourhood of `0`, supplying `hv`.

The ONLY remaining hypothesis is the top-level metric regularity `hC` (genuine, non-vacuous — NOT a
no-conjugate hypothesis).  The domain is HONEST: a neighbourhood of the RNC centre only.  This is the
1st-order sibling of the `(b)`-side van-Vleck −Ric closer.  It is NOT `a₁ = R/6`. -/
theorem expJacobianDet_radialDeriv_real_uncond (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p : Point n) :
    ∀ᶠ v in 𝓝 (0 : Point n),
      ∃ Bd : Matrix (Fin n) (Fin n) ℝ,
        HasDerivAt (fun s : ℝ => s • QIQTH.JacobianDet.expJacobianMat g gi hC p (s • v)) Bd 1 ∧
        radialDeriv (fun x => Real.log (QIQTH.JacobianDet.expJacobianDet g gi hC p x)) v
          = (Bd * (QIQTH.JacobianDet.expJacobianMat g gi hC p v)⁻¹).trace - (n : ℝ) := by
  -- The exp-ball is a neighbourhood of `0`, so `‖v‖ < expRho` holds eventually.
  have hball : ∀ᶠ v in 𝓝 (0 : Point n), ‖v‖ < expRho g gi hC p := by
    have hmem : Metric.ball (0 : Point n) (expRho g gi hC p) ∈ 𝓝 (0 : Point n) :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (expRho_pos g gi hC p))
    filter_upwards [hmem] with v hv
    simpa only [Metric.mem_ball, dist_zero_right] using hv
  -- `J > 0` near `0` upgrades (via `eventually_eventually_nhds`) to: for `v` near `0`,
  -- `J > 0` on a whole neighbourhood of `v`.
  have hnbhd : ∀ᶠ v in 𝓝 (0 : Point n),
      ∀ᶠ x in 𝓝 v, 0 < QIQTH.JacobianDet.expJacobianDet g gi hC p x :=
    eventually_eventually_nhds.2 (QIQTH.JacobianRadial.expJacobianDet_pos_nhds g gi hC p)
  filter_upwards [hball, hnbhd] with v hv hVnhd
  -- `hJv` — positivity AT `v`.
  have hJv : 0 < QIQTH.JacobianDet.expJacobianDet g gi hC p v := hVnhd.self_of_nhds
  -- `hpos` — positivity along the ray, from positivity on `𝓝 v`.
  have hpos : ∀ᶠ s in nhds (1 : ℝ),
      0 < QIQTH.JacobianDet.expJacobianDet g gi hC p (s • v) :=
    expJacobianDet_pos_ray_of_pos_nhds g gi hC p v hVnhd
  -- Discharge the conditional first-derivative identity.
  exact expJacobianDet_radialDeriv_real g gi hC p v hv hJv hpos

end QIQTH.JacobianRegularity
