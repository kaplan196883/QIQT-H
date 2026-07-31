/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet4D

/-!
# JET-4 TOWER — rung J4-5d1: the `l`-uniform SECOND→THIRD variation residual

This file lands `expJet3SecondVar_residual_Icc_unif`, the `l`-uniform second-variation residual
one Fréchet order up from `expJet2FirstVar_residual_Icc_unif` (`ExpMapContDiff3.lean:3474`).

Where the Rung-3 first-variation residual controls
`‖Φ_{v+l}(t)(ι h) − Φ_v(t)(ι h) − Q^{hl}_v(t)‖ ≤ C·‖h‖·‖l‖²`, this one controls the analogous
SECOND-variation residual against the genuine third-variation curve:
`‖Q^{hk}_{v+l}(t) − Q^{hk}_v(t) − R^{hkl}_v(t)‖ ≤ C·‖h‖·‖k‖·‖l‖²`, uniformly on `[0,1]`, with a single
constant `C₀ ≥ 0` valid for EVERY varied direction `l` (`‖v+l‖ ≤ expRho`) and every `v+l`-propagator
`Φ'`.  `Q^{hk}` is the genuine second-variation curve `expJet2Curve`; `R^{hkl}` is the genuine
third-variation curve `expJet3Curve`.

The `O(‖l‖²)` conclusion is DERIVED — NOT carried — via the `[0,1]`-uniform vector Grönwall
(`gronwall_vec_residual_Icc`) fed by:
* the residual ODE `expJet3_residual_hasDerivWithinAt` (the second-variation difference vs the third
  variation solves `S' = DF(Y_v)(S) + ρ`), and
* the `l`-uniform Jet₃ quadratic remainder `expJet3_remainder_quadratic_bound_unif` bounding the
  source `‖ρ(t)‖ ≤ Cr·‖h‖·‖k‖·‖l‖²`.

This is the exact datum the order-4 `_unif` remainder brick (J4-5d2) consumes as its `hFQ*` inputs
in `expJet4_remainder_quadratic_bound'` (`ExpJet4RemainderP.lean`).
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

variable {n : ℕ}

set_option maxHeartbeats 1600000 in
/-- **The `l`-UNIFORM `‖h‖‖k‖`-separated second-variation residual, quadratic in `l`.**  The
    `l`-uniform mirror of `expJet2FirstVar_residual_Icc_unif` one Fréchet order up: a single
    `C₀ ≥ 0` works for EVERY varied direction `l` (`‖v+l‖ ≤ expRho`) and every `v+l`-propagator `Φ'`,
    controlling the second-variation difference against the genuine third variation
    `‖Q^{hk}_{v+l}(t) − Q^{hk}_v(t) − R^{hkl}_v(t)‖ ≤ C₀·‖h‖·‖k‖·‖l‖²` on `[0,1]`, with `Q^{hk}` the
    genuine second-variation curve `expJet2Curve` and `R^{hkl}` the genuine third-variation curve
    `expJet3Curve` (whose `Q··` inputs are the second-variation curves at `v`).

    Proof (mirror of `expJet2FirstVar_residual_Icc_unif`, one order up): feed the `l`-uniform Jet₃
    remainder `expJet3_remainder_quadratic_bound_unif` (source `‖ρ‖ ≤ Cr·‖h‖·‖k‖·‖l‖²`) and the
    residual ODE `expJet3_residual_hasDerivWithinAt` into the `[0,1]`-uniform vector Grönwall
    `gronwall_vec_residual_Icc`; the outer factor `e^{Kstar}` uses the `v`-tube bound
    `expJet_fderiv_tube_bddAbove`, independent of `l`. -/
theorem expJet3SecondVar_residual_Icc_unif (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hΦd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (l : Point n) (hvl : ‖v + l‖ ≤ expRho g gi hC p),
      ∀ (Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n))),
        Φ' 0 = ContinuousLinearMap.id ℝ (Point n × Point n) →
        ∀ (hΦ'cont : ContinuousOn Φ' (Set.Icc (0 : ℝ) 1)),
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          HasDerivWithinAt Φ' (expJetPsi g gi hC p (v + l) t (Φ' t)) (Set.Icc (0 : ℝ) 1) t) →
        ∀ (h k : Point n), ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖expJet2Curve g gi hC p (v + l) Φ' hvl hΦ'cont h k t
              - expJet2Curve g gi hC p v Φ hv hΦcont h k t
              - expJet3Curve g gi hC p v Φ
                  (expJet2Curve g gi hC p v Φ hv hΦcont k l)
                  (expJet2Curve g gi hC p v Φ hv hΦcont h l)
                  (expJet2Curve g gi hC p v Φ hv hΦcont h k)
                  hv hΦcont
                  (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
                  (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
                  (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
                  h k l t‖ ≤ C₀ * ‖h‖ * ‖k‖ * ‖l‖ ^ 2 := by
  obtain ⟨Cr, hCr0, hrbdU⟩ :=
    expJet3_remainder_quadratic_bound_unif g gi hC p v Φ hv hΦ0 hΦcont hΦd
  obtain ⟨Kstar, hKstar0, hKstar⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  refine ⟨Cr * Real.exp Kstar, mul_nonneg hCr0 (Real.exp_pos _).le, ?_⟩
  intro l hvl Φ' hΦ'0 hΦ'cont hΦ'd h k t ht
  -- derivative specs of the three genuine curves (from their `expJet{2,3}Fund` witnesses).
  obtain ⟨hQv0, -, -, hQvd⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h k).choose_spec
  obtain ⟨hQw0, -, -, hQwd⟩ :=
    (expJet2Fund g gi hC p (v + l) Φ' hvl hΦ'cont h k).choose_spec
  obtain ⟨hR0, -, -, hRd⟩ :=
    (expJet3Fund g gi hC p v Φ
      (expJet2Curve g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve g gi hC p v Φ hv hΦcont h k)
      hv hΦcont
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
      h k l).choose_spec
  have hgron := gronwall_vec_residual_Icc
    (fun s => expJet2Curve g gi hC p (v + l) Φ' hvl hΦ'cont h k s
      - expJet2Curve g gi hC p v Φ hv hΦcont h k s
      - expJet3Curve g gi hC p v Φ
          (expJet2Curve g gi hC p v Φ hv hΦcont k l)
          (expJet2Curve g gi hC p v Φ hv hΦcont h l)
          (expJet2Curve g gi hC p v Φ hv hΦcont h k)
          hv hΦcont
          (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
          (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
          (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
          h k l s)
    (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + l) s)
        - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s))
          (expJet2Curve g gi hC p (v + l) Φ' hvl hΦ'cont h k s)
      + (expJet2Rhs g gi hC p (v + l) Φ' h k s
         - expJet2Rhs g gi hC p v Φ h k s
         - expJet3Rhs g gi hC p v Φ
             (expJet2Curve g gi hC p v Φ hv hΦcont k l)
             (expJet2Curve g gi hC p v Φ hv hΦcont h l)
             (expJet2Curve g gi hC p v Φ hv hΦcont h k) h k l s))
    (fun s => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) Kstar
    (Cr * ‖h‖ * ‖k‖ * ‖l‖ ^ 2)
    hKstar0
    (mul_nonneg (mul_nonneg (mul_nonneg hCr0 (norm_nonneg _)) (norm_nonneg _))
      (pow_nonneg (norm_nonneg _) 2))
    (by
      have e1 : expJet2Curve g gi hC p (v + l) Φ' hvl hΦ'cont h k 0 = 0 := hQw0
      have e2 : expJet2Curve g gi hC p v Φ hv hΦcont h k 0 = 0 := hQv0
      have e3 : expJet3Curve g gi hC p v Φ
          (expJet2Curve g gi hC p v Φ hv hΦcont k l)
          (expJet2Curve g gi hC p v Φ hv hΦcont h l)
          (expJet2Curve g gi hC p v Φ hv hΦcont h k)
          hv hΦcont
          (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
          (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
          (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
          h k l 0 = 0 := hR0
      simp only [e1, e2, e3, sub_self])
    (fun s hs => expJet3_residual_hasDerivWithinAt g gi hC p v (v + l) Φ Φ'
      (expJet2Curve g gi hC p v Φ hv hΦcont h k)
      (expJet2Curve g gi hC p (v + l) Φ' hvl hΦ'cont h k)
      (expJet2Curve g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve g gi hC p v Φ hv hΦcont h k)
      (expJet3Curve g gi hC p v Φ
        (expJet2Curve g gi hC p v Φ hv hΦcont k l)
        (expJet2Curve g gi hC p v Φ hv hΦcont h l)
        (expJet2Curve g gi hC p v Φ hv hΦcont h k)
        hv hΦcont
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
        h k l)
      h k l hQvd hQwd hRd s hs)
    hKstar (fun s hs => hrbdU l hvl Φ' hΦ'0 hΦ'cont hΦ'd h k s hs) t ht
  calc ‖expJet2Curve g gi hC p (v + l) Φ' hvl hΦ'cont h k t
          - expJet2Curve g gi hC p v Φ hv hΦcont h k t
          - expJet3Curve g gi hC p v Φ
              (expJet2Curve g gi hC p v Φ hv hΦcont k l)
              (expJet2Curve g gi hC p v Φ hv hΦcont h l)
              (expJet2Curve g gi hC p v Φ hv hΦcont h k)
              hv hΦcont
              (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
              (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
              (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
              h k l t‖
      ≤ (Cr * ‖h‖ * ‖k‖ * ‖l‖ ^ 2) * Real.exp Kstar := hgron
    _ = Cr * Real.exp Kstar * ‖h‖ * ‖k‖ * ‖l‖ ^ 2 := by ring

end QIQTH.ExpMap
