/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet4RemainderUnif
import QIQTH.ExpJet4Residual
import QIQTH.ExpJet5Phase3

/-!
# JET-5 TOWER — rung J5-5b: the `m`-uniform THIRD→FOURTH variation residual

This file lands `expJet4SecondVar_residual_Icc_unif`, the `m`-uniform third-variation residual one
Fréchet order up from `expJet3SecondVar_residual_Icc_unif` (`ExpJet3SecondVarResidual.lean`).

Where the Rung-4 residual controls
`‖Q^{hk}_{v+l}(t) − Q^{hk}_v(t) − R^{hkl}_v(t)‖ ≤ C·‖h‖·‖k‖·‖l‖²`, this one controls the analogous
THIRD-variation residual against the genuine fourth-variation curve:
`‖R^{hkl}_{v+m}(t) − R^{hkl}_v(t) − S^{hklm}_v(t)‖ ≤ C·‖h‖·‖k‖·‖l‖·‖m‖²`, uniformly on `[0,1]`, with a
single constant `C₀ ≥ 0` valid for EVERY varied direction `m` (`‖v+m‖ ≤ expRho`) and every `v+m`-
propagator `Φ'`.  `R^{hkl}` is the genuine third-variation curve `expJet3Curve`; `S^{hklm}` is the
genuine fourth-variation curve `expJet4Curve`.

The `O(‖m‖²)` conclusion is DERIVED — NOT carried — via the `[0,1]`-uniform vector Grönwall
(`gronwall_vec_residual_Icc`) fed by:
* the residual ODE `expJet4_residual_hasDerivWithinAt` (the third-variation difference vs the fourth
  variation solves `S' = DF(Y_v)(S) + ρ`), and
* the `m`-uniform Jet₄ quadratic remainder `expJet4_remainder_quadratic_bound_unif` bounding the
  source `‖ρ(t)‖ ≤ C₀·‖h‖·‖k‖·‖l‖·‖m‖²`.

This is the exact datum the order-5 `_unif` remainder brick (J5-5d) consumes as its `hFQ3*` inputs
in `expJet5_remainder_quadratic_bound_P` (`ExpJet5RemainderP.lean`).

## Honest firewall (binding)

Uniform-feeder layer ONLY.  Does NOT prove `expJet5_remainder_quadratic_bound_unif`,
`expMap_fderiv4_hasFDerivAt`, `exp ∈ C⁵`, `κ = 1/6`, the heat-kernel parametrix, or `a₁ = R/6`
(CONDITIONAL).  Every strictly-lower-order input is discharged from a proved uniform lemma.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxSynthPendingDepth 6

variable {n : ℕ}

set_option maxHeartbeats 6400000 in
/-- **The `m`-UNIFORM `‖h‖‖k‖‖l‖`-separated third-variation residual, quadratic in `m`.**  The
    `m`-uniform mirror of `expJet3SecondVar_residual_Icc_unif` one Fréchet order up: a single
    `C₀ ≥ 0` works for EVERY varied direction `m` (`‖v+m‖ ≤ expRho`) and every `v+m`-propagator `Φ'`,
    controlling the third-variation difference against the genuine fourth variation
    `‖R^{hkl}_{v+m}(t) − R^{hkl}_v(t) − S^{hklm}_v(t)‖ ≤ C₀·‖h‖·‖k‖·‖l‖·‖m‖²` on `[0,1]`, with
    `R^{hkl}` the genuine third-variation curve `expJet3Curve` and `S^{hklm}` the genuine
    fourth-variation curve `expJet4Curve`.

    Proof (mirror of `expJet3SecondVar_residual_Icc_unif`, one order up): feed the `m`-uniform Jet₄
    remainder `expJet4_remainder_quadratic_bound_unif` (source `‖ρ‖ ≤ C₀·‖h‖·‖k‖·‖l‖·‖m‖²`) and the
    residual ODE `expJet4_residual_hasDerivWithinAt` into the `[0,1]`-uniform vector Grönwall
    `gronwall_vec_residual_Icc`; the outer factor `e^{Kstar}` uses the `v`-tube bound
    `expJet_fderiv_tube_bddAbove`, independent of `m`. -/
theorem expJet4SecondVar_residual_Icc_unif (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hΦd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (m : Point n) (hvm : ‖v + m‖ ≤ expRho g gi hC p)
      (Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n))),
        Φ' 0 = ContinuousLinearMap.id ℝ (Point n × Point n) →
        ∀ (hΦ'cont : ContinuousOn Φ' (Set.Icc (0 : ℝ) 1)),
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          HasDerivWithinAt Φ' (expJetPsi g gi hC p (v + m) t (Φ' t)) (Set.Icc (0 : ℝ) 1) t) →
        ∀ (h k l : Point n), ∀ t ∈ Set.Icc (0 : ℝ) 1,
          ‖expJet3Curve g gi hC p (v + m) Φ'
                (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont k l)
                (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h l)
                (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h k)
                hvm hΦ'cont
                (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont k l)
                (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont h l)
                (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont h k)
                h k l t
              - expJet3Curve g gi hC p v Φ
                (expJet2Curve g gi hC p v Φ hv hΦcont k l)
                (expJet2Curve g gi hC p v Φ hv hΦcont h l)
                (expJet2Curve g gi hC p v Φ hv hΦcont h k)
                hv hΦcont
                (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
                (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
                (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
                h k l t
              - expJet4Curve g gi hC p v Φ
                (expJet2Curve g gi hC p v Φ hv hΦcont h k)
                (expJet2Curve g gi hC p v Φ hv hΦcont h l)
                (expJet2Curve g gi hC p v Φ hv hΦcont h m)
                (expJet2Curve g gi hC p v Φ hv hΦcont k l)
                (expJet2Curve g gi hC p v Φ hv hΦcont k m)
                (expJet2Curve g gi hC p v Φ hv hΦcont l m)
                (expJet3Curve g gi hC p v Φ
                   (expJet2Curve g gi hC p v Φ hv hΦcont k l)
                   (expJet2Curve g gi hC p v Φ hv hΦcont h l)
                   (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l)
                (expJet3Curve g gi hC p v Φ
                   (expJet2Curve g gi hC p v Φ hv hΦcont k m)
                   (expJet2Curve g gi hC p v Φ hv hΦcont h m)
                   (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m)
                (expJet3Curve g gi hC p v Φ
                   (expJet2Curve g gi hC p v Φ hv hΦcont l m)
                   (expJet2Curve g gi hC p v Φ hv hΦcont h m)
                   (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m)
                (expJet3Curve g gi hC p v Φ
                   (expJet2Curve g gi hC p v Φ hv hΦcont l m)
                   (expJet2Curve g gi hC p v Φ hv hΦcont k m)
                   (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m)
                hv hΦcont
                (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
                (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
                (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
                (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
                (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
                (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
                (expJet3Curve_continuousOn g gi hC p v Φ
                   (expJet2Curve g gi hC p v Φ hv hΦcont k l)
                   (expJet2Curve g gi hC p v Φ hv hΦcont h l)
                   (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l)
                (expJet3Curve_continuousOn g gi hC p v Φ
                   (expJet2Curve g gi hC p v Φ hv hΦcont k m)
                   (expJet2Curve g gi hC p v Φ hv hΦcont h m)
                   (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m)
                (expJet3Curve_continuousOn g gi hC p v Φ
                   (expJet2Curve g gi hC p v Φ hv hΦcont l m)
                   (expJet2Curve g gi hC p v Φ hv hΦcont h m)
                   (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m)
                (expJet3Curve_continuousOn g gi hC p v Φ
                   (expJet2Curve g gi hC p v Φ hv hΦcont l m)
                   (expJet2Curve g gi hC p v Φ hv hΦcont k m)
                   (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
                   (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m)
                h k l m t‖ ≤ C₀ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 := by
  obtain ⟨Cr, hCr0, hrbdU⟩ :=
    expJet4_remainder_quadratic_bound_unif g gi hC p v Φ hv hΦ0 hΦcont hΦd
  obtain ⟨Kstar, hKstar0, hKstar⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv
  refine ⟨Cr * Real.exp Kstar, mul_nonneg hCr0 (Real.exp_pos _).le, ?_⟩
  intro m hvm Φ' hΦ'0 hΦ'cont hΦ'd h k l t ht
  -- derivative specs of the three genuine curves (from their `expJet{3,4}Fund` witnesses).
  obtain ⟨hQv0, -, -, hQvd⟩ := (expJet3Fund g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l).choose_spec
  obtain ⟨hQw0, -, -, hQwd⟩ := (expJet3Fund g gi hC p (v + m) Φ'
    (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont k l)
    (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h l)
    (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h k) hvm hΦ'cont
    (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont k l)
    (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont h l)
    (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont h k) h k l).choose_spec
  obtain ⟨hR0, -, -, hRd⟩ := (expJet4Fund g gi hC p v Φ
    (expJet2Curve g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve g gi hC p v Φ hv hΦcont l m)
    (expJet3Curve g gi hC p v Φ
       (expJet2Curve g gi hC p v Φ hv hΦcont k l)
       (expJet2Curve g gi hC p v Φ hv hΦcont h l)
       (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l)
    (expJet3Curve g gi hC p v Φ
       (expJet2Curve g gi hC p v Φ hv hΦcont k m)
       (expJet2Curve g gi hC p v Φ hv hΦcont h m)
       (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m)
    (expJet3Curve g gi hC p v Φ
       (expJet2Curve g gi hC p v Φ hv hΦcont l m)
       (expJet2Curve g gi hC p v Φ hv hΦcont h m)
       (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m)
    (expJet3Curve g gi hC p v Φ
       (expJet2Curve g gi hC p v Φ hv hΦcont l m)
       (expJet2Curve g gi hC p v Φ hv hΦcont k m)
       (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m)
    hv hΦcont
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
    (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
    (expJet3Curve_continuousOn g gi hC p v Φ
       (expJet2Curve g gi hC p v Φ hv hΦcont k l)
       (expJet2Curve g gi hC p v Φ hv hΦcont h l)
       (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l)
    (expJet3Curve_continuousOn g gi hC p v Φ
       (expJet2Curve g gi hC p v Φ hv hΦcont k m)
       (expJet2Curve g gi hC p v Φ hv hΦcont h m)
       (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m)
    (expJet3Curve_continuousOn g gi hC p v Φ
       (expJet2Curve g gi hC p v Φ hv hΦcont l m)
       (expJet2Curve g gi hC p v Φ hv hΦcont h m)
       (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m)
    (expJet3Curve_continuousOn g gi hC p v Φ
       (expJet2Curve g gi hC p v Φ hv hΦcont l m)
       (expJet2Curve g gi hC p v Φ hv hΦcont k m)
       (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
       (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m)
    h k l m).choose_spec
  have hgron := gronwall_vec_residual_Icc
    (fun s => expJet3Curve g gi hC p (v + m) Φ'
        (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont k l)
        (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h l)
        (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h k)
        hvm hΦ'cont
        (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont k l)
        (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont h l)
        (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont h k)
        h k l s
      - expJet3Curve g gi hC p v Φ
        (expJet2Curve g gi hC p v Φ hv hΦcont k l)
        (expJet2Curve g gi hC p v Φ hv hΦcont h l)
        (expJet2Curve g gi hC p v Φ hv hΦcont h k)
        hv hΦcont
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
        h k l s
      - expJet4Curve g gi hC p v Φ
        (expJet2Curve g gi hC p v Φ hv hΦcont h k)
        (expJet2Curve g gi hC p v Φ hv hΦcont h l)
        (expJet2Curve g gi hC p v Φ hv hΦcont h m)
        (expJet2Curve g gi hC p v Φ hv hΦcont k l)
        (expJet2Curve g gi hC p v Φ hv hΦcont k m)
        (expJet2Curve g gi hC p v Φ hv hΦcont l m)
        (expJet3Curve g gi hC p v Φ
           (expJet2Curve g gi hC p v Φ hv hΦcont k l)
           (expJet2Curve g gi hC p v Φ hv hΦcont h l)
           (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l)
        (expJet3Curve g gi hC p v Φ
           (expJet2Curve g gi hC p v Φ hv hΦcont k m)
           (expJet2Curve g gi hC p v Φ hv hΦcont h m)
           (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m)
        (expJet3Curve g gi hC p v Φ
           (expJet2Curve g gi hC p v Φ hv hΦcont l m)
           (expJet2Curve g gi hC p v Φ hv hΦcont h m)
           (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m)
        (expJet3Curve g gi hC p v Φ
           (expJet2Curve g gi hC p v Φ hv hΦcont l m)
           (expJet2Curve g gi hC p v Φ hv hΦcont k m)
           (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m)
        hv hΦcont
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
        (expJet3Curve_continuousOn g gi hC p v Φ
           (expJet2Curve g gi hC p v Φ hv hΦcont k l)
           (expJet2Curve g gi hC p v Φ hv hΦcont h l)
           (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l)
        (expJet3Curve_continuousOn g gi hC p v Φ
           (expJet2Curve g gi hC p v Φ hv hΦcont k m)
           (expJet2Curve g gi hC p v Φ hv hΦcont h m)
           (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m)
        (expJet3Curve_continuousOn g gi hC p v Φ
           (expJet2Curve g gi hC p v Φ hv hΦcont l m)
           (expJet2Curve g gi hC p v Φ hv hΦcont h m)
           (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m)
        (expJet3Curve_continuousOn g gi hC p v Φ
           (expJet2Curve g gi hC p v Φ hv hΦcont l m)
           (expJet2Curve g gi hC p v Φ hv hΦcont k m)
           (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m)
        h k l m s)
    (fun s => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + m) s)
        - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s))
          (expJet3Curve g gi hC p (v + m) Φ'
            (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont k l)
            (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h l)
            (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h k)
            hvm hΦ'cont
            (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont k l)
            (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont h l)
            (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont h k)
            h k l s)
      + (expJet3Rhs g gi hC p (v + m) Φ'
             (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont k l)
             (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h l)
             (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h k) h k l s
         - expJet3Rhs g gi hC p v Φ
             (expJet2Curve g gi hC p v Φ hv hΦcont k l)
             (expJet2Curve g gi hC p v Φ hv hΦcont h l)
             (expJet2Curve g gi hC p v Φ hv hΦcont h k) h k l s
         - expJet4Rhs g gi hC p v Φ
             (expJet2Curve g gi hC p v Φ hv hΦcont h k)
             (expJet2Curve g gi hC p v Φ hv hΦcont h l)
             (expJet2Curve g gi hC p v Φ hv hΦcont h m)
             (expJet2Curve g gi hC p v Φ hv hΦcont k l)
             (expJet2Curve g gi hC p v Φ hv hΦcont k m)
             (expJet2Curve g gi hC p v Φ hv hΦcont l m)
             (expJet3Curve g gi hC p v Φ
                (expJet2Curve g gi hC p v Φ hv hΦcont k l)
                (expJet2Curve g gi hC p v Φ hv hΦcont h l)
                (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
                (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
                (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
                (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l)
             (expJet3Curve g gi hC p v Φ
                (expJet2Curve g gi hC p v Φ hv hΦcont k m)
                (expJet2Curve g gi hC p v Φ hv hΦcont h m)
                (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
                (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
                (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
                (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m)
             (expJet3Curve g gi hC p v Φ
                (expJet2Curve g gi hC p v Φ hv hΦcont l m)
                (expJet2Curve g gi hC p v Φ hv hΦcont h m)
                (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont
                (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
                (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
                (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m)
             (expJet3Curve g gi hC p v Φ
                (expJet2Curve g gi hC p v Φ hv hΦcont l m)
                (expJet2Curve g gi hC p v Φ hv hΦcont k m)
                (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont
                (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
                (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
                (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m)
             h k l m s))
    (fun s => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v s)) Kstar
    (Cr * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2)
    hKstar0
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCr0 (norm_nonneg _)) (norm_nonneg _))
      (norm_nonneg _)) (pow_nonneg (norm_nonneg _) 2))
    (by
      simp only [expJet3Curve, expJet4Curve] at hR0 ⊢
      simp only [hQw0, hQv0, hR0, sub_self])
    (fun s hs => expJet4_residual_hasDerivWithinAt g gi hC p v (v + m) Φ Φ'
      (expJet3Curve g gi hC p v Φ
        (expJet2Curve g gi hC p v Φ hv hΦcont k l)
        (expJet2Curve g gi hC p v Φ hv hΦcont h l)
        (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l)
      (expJet3Curve g gi hC p (v + m) Φ'
        (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont k l)
        (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h l)
        (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h k) hvm hΦ'cont
        (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont k l)
        (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont h l)
        (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont h k) h k l)
      (expJet2Curve g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve g gi hC p v Φ hv hΦcont h k)
      (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont k l)
      (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h l)
      (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h k)
      (expJet2Curve g gi hC p v Φ hv hΦcont h k)
      (expJet2Curve g gi hC p v Φ hv hΦcont h l)
      (expJet2Curve g gi hC p v Φ hv hΦcont h m)
      (expJet2Curve g gi hC p v Φ hv hΦcont k l)
      (expJet2Curve g gi hC p v Φ hv hΦcont k m)
      (expJet2Curve g gi hC p v Φ hv hΦcont l m)
      (expJet3Curve g gi hC p v Φ
         (expJet2Curve g gi hC p v Φ hv hΦcont k l)
         (expJet2Curve g gi hC p v Φ hv hΦcont h l)
         (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
         (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
         (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
         (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l)
      (expJet3Curve g gi hC p v Φ
         (expJet2Curve g gi hC p v Φ hv hΦcont k m)
         (expJet2Curve g gi hC p v Φ hv hΦcont h m)
         (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
         (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
         (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
         (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m)
      (expJet3Curve g gi hC p v Φ
         (expJet2Curve g gi hC p v Φ hv hΦcont l m)
         (expJet2Curve g gi hC p v Φ hv hΦcont h m)
         (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont
         (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
         (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
         (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m)
      (expJet3Curve g gi hC p v Φ
         (expJet2Curve g gi hC p v Φ hv hΦcont l m)
         (expJet2Curve g gi hC p v Φ hv hΦcont k m)
         (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont
         (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
         (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
         (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m)
      (expJet4Curve g gi hC p v Φ
        (expJet2Curve g gi hC p v Φ hv hΦcont h k)
        (expJet2Curve g gi hC p v Φ hv hΦcont h l)
        (expJet2Curve g gi hC p v Φ hv hΦcont h m)
        (expJet2Curve g gi hC p v Φ hv hΦcont k l)
        (expJet2Curve g gi hC p v Φ hv hΦcont k m)
        (expJet2Curve g gi hC p v Φ hv hΦcont l m)
        (expJet3Curve g gi hC p v Φ
           (expJet2Curve g gi hC p v Φ hv hΦcont k l)
           (expJet2Curve g gi hC p v Φ hv hΦcont h l)
           (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l)
        (expJet3Curve g gi hC p v Φ
           (expJet2Curve g gi hC p v Φ hv hΦcont k m)
           (expJet2Curve g gi hC p v Φ hv hΦcont h m)
           (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m)
        (expJet3Curve g gi hC p v Φ
           (expJet2Curve g gi hC p v Φ hv hΦcont l m)
           (expJet2Curve g gi hC p v Φ hv hΦcont h m)
           (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m)
        (expJet3Curve g gi hC p v Φ
           (expJet2Curve g gi hC p v Φ hv hΦcont l m)
           (expJet2Curve g gi hC p v Φ hv hΦcont k m)
           (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m)
        hv hΦcont
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
        (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
        (expJet3Curve_continuousOn g gi hC p v Φ
           (expJet2Curve g gi hC p v Φ hv hΦcont k l)
           (expJet2Curve g gi hC p v Φ hv hΦcont h l)
           (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l)
        (expJet3Curve_continuousOn g gi hC p v Φ
           (expJet2Curve g gi hC p v Φ hv hΦcont k m)
           (expJet2Curve g gi hC p v Φ hv hΦcont h m)
           (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m)
        (expJet3Curve_continuousOn g gi hC p v Φ
           (expJet2Curve g gi hC p v Φ hv hΦcont l m)
           (expJet2Curve g gi hC p v Φ hv hΦcont h m)
           (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m)
        (expJet3Curve_continuousOn g gi hC p v Φ
           (expJet2Curve g gi hC p v Φ hv hΦcont l m)
           (expJet2Curve g gi hC p v Φ hv hΦcont k m)
           (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
           (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m)
        h k l m)
      h k l m hQvd hQwd hRd s hs)
    hKstar
    (fun s hs => hrbdU m hvm Φ' hΦ'0 hΦ'cont hΦ'd h k l s hs) t ht
  calc ‖expJet3Curve g gi hC p (v + m) Φ'
          (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont k l)
          (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h l)
          (expJet2Curve g gi hC p (v + m) Φ' hvm hΦ'cont h k)
          hvm hΦ'cont
          (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont k l)
          (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont h l)
          (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm hΦ'cont h k)
          h k l t
        - expJet3Curve g gi hC p v Φ
          (expJet2Curve g gi hC p v Φ hv hΦcont k l)
          (expJet2Curve g gi hC p v Φ hv hΦcont h l)
          (expJet2Curve g gi hC p v Φ hv hΦcont h k)
          hv hΦcont
          (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
          (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
          (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
          h k l t
        - expJet4Curve g gi hC p v Φ
          (expJet2Curve g gi hC p v Φ hv hΦcont h k)
          (expJet2Curve g gi hC p v Φ hv hΦcont h l)
          (expJet2Curve g gi hC p v Φ hv hΦcont h m)
          (expJet2Curve g gi hC p v Φ hv hΦcont k l)
          (expJet2Curve g gi hC p v Φ hv hΦcont k m)
          (expJet2Curve g gi hC p v Φ hv hΦcont l m)
          (expJet3Curve g gi hC p v Φ
             (expJet2Curve g gi hC p v Φ hv hΦcont k l)
             (expJet2Curve g gi hC p v Φ hv hΦcont h l)
             (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
             (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
             (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
             (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l)
          (expJet3Curve g gi hC p v Φ
             (expJet2Curve g gi hC p v Φ hv hΦcont k m)
             (expJet2Curve g gi hC p v Φ hv hΦcont h m)
             (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
             (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
             (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
             (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m)
          (expJet3Curve g gi hC p v Φ
             (expJet2Curve g gi hC p v Φ hv hΦcont l m)
             (expJet2Curve g gi hC p v Φ hv hΦcont h m)
             (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont
             (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
             (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
             (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m)
          (expJet3Curve g gi hC p v Φ
             (expJet2Curve g gi hC p v Φ hv hΦcont l m)
             (expJet2Curve g gi hC p v Φ hv hΦcont k m)
             (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont
             (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
             (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
             (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m)
          hv hΦcont
          (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k)
          (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
          (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
          (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
          (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
          (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
          (expJet3Curve_continuousOn g gi hC p v Φ
             (expJet2Curve g gi hC p v Φ hv hΦcont k l)
             (expJet2Curve g gi hC p v Φ hv hΦcont h l)
             (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
             (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l)
             (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l)
             (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l)
          (expJet3Curve_continuousOn g gi hC p v Φ
             (expJet2Curve g gi hC p v Φ hv hΦcont k m)
             (expJet2Curve g gi hC p v Φ hv hΦcont h m)
             (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont
             (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
             (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
             (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m)
          (expJet3Curve_continuousOn g gi hC p v Φ
             (expJet2Curve g gi hC p v Φ hv hΦcont l m)
             (expJet2Curve g gi hC p v Φ hv hΦcont h m)
             (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont
             (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
             (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m)
             (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m)
          (expJet3Curve_continuousOn g gi hC p v Φ
             (expJet2Curve g gi hC p v Φ hv hΦcont l m)
             (expJet2Curve g gi hC p v Φ hv hΦcont k m)
             (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont
             (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m)
             (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m)
             (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m)
          h k l m t‖
      ≤ (Cr * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2) * Real.exp Kstar := hgron
    _ = Cr * Real.exp Kstar * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 := by ring

end QIQTH.ExpMap
