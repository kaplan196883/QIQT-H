/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet4RemainderUnif
import QIQTH.ExpJet4Residual
import QIQTH.ExpJet4DFull
import QIQTH.ExpMapContDiff3

/-!
# JET-4 TOWER — rung J4-5e: `fderiv³ exp_p` is Fréchet-differentiable with derivative `D⁴_v`.

This file lands `expMap_fderiv3_hasFDerivAt`, the faithful one-Fréchet-order-up mirror of the Rung-3
capstone `expMap_fderiv2_hasFDerivAt` (`ExpMapContDiff3.lean:3898`).  For `‖v‖ < expRho` and the
first-variation propagator witness `Φ` at `v`,

  `HasFDerivAt (w ↦ fderiv³ exp_p w) (expJetD4 … v Φ) v`.

The `HasFDerivAt` is DERIVED — never carried — by the genuine little-o argument: the `m`-uniform
`‖h‖‖k‖‖l‖`-separated Jet₄ source bound (`expJet4_remainder_quadratic_bound_unif`) fed through the
order-4 residual Grönwall (`expJet4_residual_bound`) and projected by `π` gives, for every direction
triple `(h,k,l)`, `‖A_m h k l‖ ≤ (C₀·e^{Kstar})·‖m‖²·‖l‖·‖k‖·‖h‖`; hence `‖A_m‖ ≤ Mc·‖m‖²`
(`Mc = C₀·e^{Kstar}`, three nested `opNorm_le_bound`/`opNorm_le_bound₂`) where
`A_m = fderiv³exp_p(v+m) − fderiv³exp_p(v) − D⁴_v m`; then `Mc·‖m‖² = o(‖m‖)` as `m → 0`.

This is the third-derivative differentiability datum of `exp_p`; it does NOT by itself give
`ContDiff⁴` (continuity of `v ↦ D⁴_v` is the next step), NOT `κ = 1/6`, NOT the heat kernel /
`a₁ = R/6`, NOT QG.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 800000
set_option maxSynthPendingDepth 6

variable {n : ℕ}

/-- **Rung-4 capstone (B-asm-4): `fderiv³ exp_p` is Fréchet-differentiable with derivative `D⁴_v`.**
    For `‖v‖ < expRho` and the first-variation propagator witness `Φ` at `v` (an
    `hasFDerivAt_expMap` witness with the `fderiv` identity `fderiv exp_p v = π∘(Φ 1)∘ι`),
    `HasFDerivAt (w ↦ fderiv³ exp_p w) (D⁴_v) v` with `D⁴_v = expJetD4 … v Φ`.  Proof (mirror of the
    Rung-3 `expMap_fderiv2_hasFDerivAt` one Fréchet order up): the `m`-UNIFORM `‖h‖‖k‖‖l‖`-separated
    Jet₄ source bound (`expJet4_remainder_quadratic_bound_unif`) fed through the residual Grönwall
    (`expJet4_residual_bound`) and projected by `π` gives, for every direction triple `(h,k,l)`,
    `‖A_m h k l‖ ≤ (C₀·e^{Kstar})·‖m‖²·‖l‖·‖k‖·‖h‖`; hence `‖A_m‖ ≤ Mc·‖m‖²`
    (`Mc = C₀·e^{Kstar}`, three nested `opNorm_le_bound`) where
    `A_m = fderiv³exp_p(v+m) − fderiv³exp_p(v) − D⁴_v m`; then `Mc·‖m‖² = o(‖m‖)` as `m → 0`
    (`hasFDerivAt_iff_isLittleO_nhds_zero`, radius `min (expRho−‖v‖) (c/(Mc+1))`).  This is the
    third-derivative differentiability datum of `exp_p`; it does NOT by itself give `ContDiff⁴`
    (continuity of `v ↦ D⁴_v` is the next step), NOT `κ = 1/6`, NOT the heat kernel / `a₁ = R/6`,
    NOT QG. -/
theorem expMap_fderiv3_hasFDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ < expRho g gi hC p)
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hΦderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t)
    (hfdv : fderiv ℝ (expMap g gi hC p) v
      = expJetPi.comp ((Φ 1).comp (expJetIota (n := n)))) :
    HasFDerivAt (fun w => fderiv ℝ (fun z => fderiv ℝ (fun u => fderiv ℝ (expMap g gi hC p) u) z) w)
      (expJetD4 g gi hC p v Φ hv.le hΦcont) v := by
  obtain ⟨C₀, hC₀0, hrbdU⟩ :=
    expJet4_remainder_quadratic_bound_unif g gi hC p v Φ hv.le hΦ0 hΦcont hΦderiv
  obtain ⟨Kstar, hKstar0, hKstar⟩ := expJet_fderiv_tube_bddAbove g gi hC p v hv.le
  set Mc : ℝ := C₀ * Real.exp Kstar with hMcdef
  have hMc0 : 0 ≤ Mc := mul_nonneg hC₀0 (Real.exp_pos _).le
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  rw [Metric.eventually_nhds_iff]
  refine ⟨min (expRho g gi hC p - ‖v‖) (c / (Mc + 1)),
    lt_min (by linarith [hv]) (div_pos hc (by linarith)), fun m hm => ?_⟩
  rw [dist_eq_norm, sub_zero] at hm
  have hm1 : ‖m‖ < expRho g gi hC p - ‖v‖ := lt_of_lt_of_le hm (min_le_left _ _)
  have hmM : ‖m‖ ≤ c / (Mc + 1) := (lt_of_lt_of_le hm (min_le_right _ _)).le
  have hvm_lt : ‖v + m‖ < expRho g gi hC p :=
    lt_of_le_of_lt (norm_add_le v m) (by linarith)
  have hvm_le : ‖v + m‖ ≤ expRho g gi hC p := hvm_lt.le
  -- the `v+m` first-variation propagator witness + the `fderiv exp_p` identity there.
  obtain ⟨Φ', hΦ'0, hΦ'deriv, hfdvm'⟩ := hasFDerivAt_expMap g gi hC p (v + m) hvm_lt
  have hΦ'cont : ContinuousOn Φ' (Set.Icc (0 : ℝ) 1) :=
    fun t ht => (hΦ'deriv t ht).continuousWithinAt
  have hfd_vm : fderiv ℝ (expMap g gi hC p) (v + m)
      = expJetPi.comp ((Φ' 1).comp (expJetIota (n := n))) := hfdvm'.fderiv
  -- the `fderiv³` (= `fderiv` of the second-derivative map) identities at `v` and `v+m`
  -- (from the Rung-3 capstone).
  have hfd3_v : fderiv ℝ (fun z => fderiv ℝ (fun u => fderiv ℝ (expMap g gi hC p) u) z) v
      = expJetD3 g gi hC p v Φ hv.le hΦcont :=
    (expMap_fderiv2_hasFDerivAt g gi hC p v Φ hv hΦ0 hΦcont hΦderiv hfdv).fderiv
  have hfd3_vm : fderiv ℝ (fun z => fderiv ℝ (fun u => fderiv ℝ (expMap g gi hC p) u) z) (v + m)
      = expJetD3 g gi hC p (v + m) Φ' hvm_le hΦ'cont :=
    (expMap_fderiv2_hasFDerivAt g gi hC p (v + m) Φ' hvm_lt hΦ'0 hΦ'cont hΦ'deriv hfd_vm).fderiv
  -- the `m`-uniform operator-norm bound `‖A_m‖ ≤ Mc·‖m‖²`.
  have hAm : ‖fderiv ℝ (fun z => fderiv ℝ (fun u => fderiv ℝ (expMap g gi hC p) u) z) (v + m)
      - fderiv ℝ (fun z => fderiv ℝ (fun u => fderiv ℝ (expMap g gi hC p) u) z) v
      - expJetD4 g gi hC p v Φ hv.le hΦcont m‖ ≤ Mc * ‖m‖ ^ 2 := by
    rw [hfd3_v, hfd3_vm]
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hMc0 (sq_nonneg _)) (fun l => ?_)
    refine ContinuousLinearMap.opNorm_le_bound₂ _
      (mul_nonneg (mul_nonneg hMc0 (sq_nonneg _)) (norm_nonneg _)) (fun k h => ?_)
    -- the genuine third-variation curve at `v` and `v+m` (via `expJet3CurveG` = order-3 fund choose).
    obtain ⟨hQv0, -, -, hQvd⟩ :=
      (expJet3Fund g gi hC p v Φ
        (expJet2Curve g gi hC p v Φ hv.le hΦcont k l)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont h l)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont h k) hv.le hΦcont
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont k l)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont h l)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont h k) h k l).choose_spec
    obtain ⟨hQw0, -, -, hQwd⟩ :=
      (expJet3Fund g gi hC p (v + m) Φ'
        (expJet2Curve g gi hC p (v + m) Φ' hvm_le hΦ'cont k l)
        (expJet2Curve g gi hC p (v + m) Φ' hvm_le hΦ'cont h l)
        (expJet2Curve g gi hC p (v + m) Φ' hvm_le hΦ'cont h k) hvm_le hΦ'cont
        (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm_le hΦ'cont k l)
        (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm_le hΦ'cont h l)
        (expJet2Curve_continuousOn g gi hC p (v + m) Φ' hvm_le hΦ'cont h k) h k l).choose_spec
    -- the genuine fourth-variation curve `R` at `v` (order-4 fund choose).
    obtain ⟨hR0, -, -, hRd⟩ :=
      (expJet4Fund g gi hC p v Φ
        (expJet2Curve g gi hC p v Φ hv.le hΦcont h k)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont h l)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont h m)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont k l)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont k m)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont l m)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont h k l)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont h k m)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont h l m)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont k l m)
        hv.le hΦcont
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont h k)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont h l)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont h m)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont k l)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont k m)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont l m)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h k l)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h k m)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h l m)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont k l m) h k l m).choose_spec
    have hρ0 : (0 : ℝ) ≤ C₀ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2 :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC₀0 (norm_nonneg _)) (norm_nonneg _))
        (norm_nonneg _)) (sq_nonneg _)
    have hres := expJet4_residual_bound g gi hC p v (v + m) Φ Φ'
      (expJet3CurveG g gi hC p v Φ hv.le hΦcont h k l)
      (expJet3CurveG g gi hC p (v + m) Φ' hvm_le hΦ'cont h k l)
      (expJet2Curve g gi hC p v Φ hv.le hΦcont k l)
      (expJet2Curve g gi hC p v Φ hv.le hΦcont h l)
      (expJet2Curve g gi hC p v Φ hv.le hΦcont h k)
      (expJet2Curve g gi hC p (v + m) Φ' hvm_le hΦ'cont k l)
      (expJet2Curve g gi hC p (v + m) Φ' hvm_le hΦ'cont h l)
      (expJet2Curve g gi hC p (v + m) Φ' hvm_le hΦ'cont h k)
      (expJet2Curve g gi hC p v Φ hv.le hΦcont h k)
      (expJet2Curve g gi hC p v Φ hv.le hΦcont h l)
      (expJet2Curve g gi hC p v Φ hv.le hΦcont h m)
      (expJet2Curve g gi hC p v Φ hv.le hΦcont k l)
      (expJet2Curve g gi hC p v Φ hv.le hΦcont k m)
      (expJet2Curve g gi hC p v Φ hv.le hΦcont l m)
      (expJet3CurveG g gi hC p v Φ hv.le hΦcont h k l)
      (expJet3CurveG g gi hC p v Φ hv.le hΦcont h k m)
      (expJet3CurveG g gi hC p v Φ hv.le hΦcont h l m)
      (expJet3CurveG g gi hC p v Φ hv.le hΦcont k l m)
      (expJet4Fund g gi hC p v Φ
        (expJet2Curve g gi hC p v Φ hv.le hΦcont h k)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont h l)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont h m)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont k l)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont k m)
        (expJet2Curve g gi hC p v Φ hv.le hΦcont l m)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont h k l)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont h k m)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont h l m)
        (expJet3CurveG g gi hC p v Φ hv.le hΦcont k l m)
        hv.le hΦcont
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont h k)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont h l)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont h m)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont k l)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont k m)
        (expJet2Curve_continuousOn g gi hC p v Φ hv.le hΦcont l m)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h k l)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h k m)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont h l m)
        (expJet3CurveG_continuousOn g gi hC p v Φ hv.le hΦcont k l m) h k l m).choose
      h k l m hQv0 hQw0 hR0 hQvd hQwd hRd Kstar
      (C₀ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2) hKstar0 hρ0 hKstar
      (fun t ht => hrbdU m hvm_le Φ' hΦ'0 hΦ'cont hΦ'deriv h k l t ht)
    simp only [ContinuousLinearMap.sub_apply]
    rw [expJetD3_apply, expJetD3_apply, expJetD4_apply]
    calc ‖expJetPi (expJet3ValG g gi hC p (v + m) Φ' hvm_le hΦ'cont h k l)
            - expJetPi (expJet3ValG g gi hC p v Φ hv.le hΦcont h k l)
            - expJetPi (expJet4ValG g gi hC p v Φ hv.le hΦcont h k l m)‖
        = ‖expJetPi (expJet3ValG g gi hC p (v + m) Φ' hvm_le hΦ'cont h k l
              - expJet3ValG g gi hC p v Φ hv.le hΦcont h k l
              - expJet4ValG g gi hC p v Φ hv.le hΦcont h k l m)‖ := by rw [map_sub, map_sub]
      _ ≤ ‖expJetPi (n := n)‖ * ‖expJet3ValG g gi hC p (v + m) Φ' hvm_le hΦ'cont h k l
              - expJet3ValG g gi hC p v Φ hv.le hΦcont h k l
              - expJet4ValG g gi hC p v Φ hv.le hΦcont h k l m‖ :=
          (expJetPi (n := n)).le_opNorm _
      _ ≤ 1 * ‖expJet3ValG g gi hC p (v + m) Φ' hvm_le hΦ'cont h k l
              - expJet3ValG g gi hC p v Φ hv.le hΦcont h k l
              - expJet4ValG g gi hC p v Φ hv.le hΦcont h k l m‖ :=
          mul_le_mul_of_nonneg_right expJetPi_opNorm_le (norm_nonneg _)
      _ = ‖expJet3ValG g gi hC p (v + m) Φ' hvm_le hΦ'cont h k l
              - expJet3ValG g gi hC p v Φ hv.le hΦcont h k l
              - expJet4ValG g gi hC p v Φ hv.le hΦcont h k l m‖ := one_mul _
      _ ≤ (C₀ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ ^ 2) * Real.exp Kstar := hres
      _ = Mc * ‖m‖ ^ 2 * ‖l‖ * ‖k‖ * ‖h‖ := by rw [hMcdef]; ring
  -- the little-o: `Mc·‖m‖² ≤ c·‖m‖` on the chosen radius.
  have hMc : Mc * ‖m‖ ≤ c := by
    have h1 : Mc * ‖m‖ ≤ Mc * (c / (Mc + 1)) := mul_le_mul_of_nonneg_left hmM hMc0
    have h2 : Mc * (c / (Mc + 1)) ≤ c := by
      rw [← mul_div_assoc, div_le_iff₀ (by linarith : (0 : ℝ) < Mc + 1)]
      nlinarith [hc, hMc0]
    linarith
  show ‖fderiv ℝ (fun z => fderiv ℝ (fun u => fderiv ℝ (expMap g gi hC p) u) z) (v + m)
      - fderiv ℝ (fun z => fderiv ℝ (fun u => fderiv ℝ (expMap g gi hC p) u) z) v
      - expJetD4 g gi hC p v Φ hv.le hΦcont m‖ ≤ c * ‖m‖
  calc ‖fderiv ℝ (fun z => fderiv ℝ (fun u => fderiv ℝ (expMap g gi hC p) u) z) (v + m)
          - fderiv ℝ (fun z => fderiv ℝ (fun u => fderiv ℝ (expMap g gi hC p) u) z) v
          - expJetD4 g gi hC p v Φ hv.le hΦcont m‖
      ≤ Mc * ‖m‖ ^ 2 := hAm
    _ = (Mc * ‖m‖) * ‖m‖ := by ring
    _ ≤ c * ‖m‖ := mul_le_mul_of_nonneg_right hMc (norm_nonneg _)

end QIQTH.ExpMap
