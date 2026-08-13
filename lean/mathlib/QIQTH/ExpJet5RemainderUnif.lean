/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet5RemainderB
import QIQTH.ExpJet5Prereq
import QIQTH.ExpJet4FundBounds
import QIQTH.ExpJet5RemAssemblyDir
import QIQTH.ExpJet5RemFactor
import QIQTH.ExpJet5UnifFeeders
import QIQTH.ExpJet4SecondVarResidual
import QIQTH.ExpJet4RemainderUnif
import QIQTH.ExpMapContDiff2
import QIQTH.ExpMapContDiff3
import QIQTH.ExpJet3SecondVarResidual

/-!
# JET-5 TOWER — rung J5-5d: the `r`-UNIFORM order-5 quadratic remainder bound

`expJet5_remainder_quadratic_bound_unif`: the `r`-uniform mirror of the directional
`expJet5_remainder_quadratic_bound_P` (`ExpJet5RemainderP.lean`), one Fréchet order up from
`expJet4_remainder_quadratic_bound_unif`.  A SINGLE `C₀ ≥ 0` — independent of the varied base
direction `r`, of the `v+r`-propagator `Φ'`, and of the probes `(h,k,l,m)` — bounds the Jet₅
residual ODE source by `C₀·‖h‖·‖k‖·‖l‖·‖m‖·‖r‖²`, written against the GENUINE `expJet{2,3,4}Curve`
variations at `v` and `v+r`.  Every carried INPUT of `expJet5_remainder_quadratic_bound_P` is
DISCHARGED internally from a proved uniform feeder lemma; the witness constant is chosen UP FRONT
from the `r`-independent uniform tube/Lipschitz data (uniform `Kstar` via
`expJet_fderiv_tube_bddAbove_unif`).

## Honest firewall (binding)

This file proves ONLY the `_unif` layer.  It does NOT prove `expMap_fderiv4_hasFDerivAt`,
`exp ∈ C⁵`, `κ = 1/6`, the heat-kernel parametrix, or `a₁ = R/6` (CONDITIONAL).  All lower-order
inputs are proved uniform lemmas.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxHeartbeats 25600000
set_option maxRecDepth 65536
set_option maxSynthPendingDepth 6
set_option synthInstance.maxHeartbeats 2000000

variable {n : ℕ}

set_option maxHeartbeats 25600000 in
/-- **Jet₅ `r`-uniform quadratic remainder bound** (`_unif`).  `r`-uniform mirror of
    `expJet5_remainder_quadratic_bound_P`, one Fréchet order up from the order-4 `_unif`. -/
theorem expJet5_remainder_quadratic_bound_unif (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v : Point n)
    (Φ : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (hv : ‖v‖ ≤ expRho g gi hC p)
    (hΦ0 : Φ 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
    (hΦcont : ContinuousOn Φ (Set.Icc (0 : ℝ) 1))
    (hΦd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Φ (expJetPsi g gi hC p v t (Φ t)) (Set.Icc (0 : ℝ) 1) t) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (r : Point n) (hvr : ‖v + r‖ ≤ expRho g gi hC p)
      (Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
      (_hΦ'0 : Φ' 0 = ContinuousLinearMap.id ℝ (Point n × Point n))
      (hΦ'cont : ContinuousOn Φ' (Set.Icc (0 : ℝ) 1))
      (hΦ'd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt Φ' (expJetPsi g gi hC p (v + r) t (Φ' t)) (Set.Icc (0 : ℝ) 1) t)
      (h k l m : Point n), ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖((fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + r) t))
           - (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)))
          ((expJet4Curve g gi hC p (v + r) Φ' (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m) (expJet3Curve g gi hC p (v + r) Φ' (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k) hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k l) (expJet3Curve g gi hC p (v + r) Φ' (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k) hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k m) (expJet3Curve g gi hC p (v + r) Φ' (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l) hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l) h l m) (expJet3Curve g gi hC p (v + r) Φ' (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l) hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l) k l m) hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m) (expJet3Curve_continuousOn g gi hC p (v + r) Φ' (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k) hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k l) (expJet3Curve_continuousOn g gi hC p (v + r) Φ' (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k) hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k m) (expJet3Curve_continuousOn g gi hC p (v + r) Φ' (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l) hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l) h l m) (expJet3Curve_continuousOn g gi hC p (v + r) Φ' (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l) hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l) k l m) h k l m) t)
         + (expJet4Rhs g gi hC p (v + r) Φ' (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m) (expJet3Curve g gi hC p (v + r) Φ' (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k) hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k l) (expJet3Curve g gi hC p (v + r) Φ' (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k) hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k m) (expJet3Curve g gi hC p (v + r) Φ' (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l) hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l) h l m) (expJet3Curve g gi hC p (v + r) Φ' (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m) (expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l) hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l) k l m) h k l m t
            - expJet4Rhs g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont h k) (expJet2Curve g gi hC p v Φ hv hΦcont h l) (expJet2Curve g gi hC p v Φ hv hΦcont h m) (expJet2Curve g gi hC p v Φ hv hΦcont k l) (expJet2Curve g gi hC p v Φ hv hΦcont k m) (expJet2Curve g gi hC p v Φ hv hΦcont l m) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont k l) (expJet2Curve g gi hC p v Φ hv hΦcont h l) (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont k m) (expJet2Curve g gi hC p v Φ hv hΦcont h m) (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont l m) (expJet2Curve g gi hC p v Φ hv hΦcont h m) (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont l m) (expJet2Curve g gi hC p v Φ hv hΦcont k m) (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m) h k l m t
            - expJet5Rhs g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont h k) (expJet2Curve g gi hC p v Φ hv hΦcont h l) (expJet2Curve g gi hC p v Φ hv hΦcont h m) (expJet2Curve g gi hC p v Φ hv hΦcont h r) (expJet2Curve g gi hC p v Φ hv hΦcont k l) (expJet2Curve g gi hC p v Φ hv hΦcont k m) (expJet2Curve g gi hC p v Φ hv hΦcont k r) (expJet2Curve g gi hC p v Φ hv hΦcont l m) (expJet2Curve g gi hC p v Φ hv hΦcont l r) (expJet2Curve g gi hC p v Φ hv hΦcont m r) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont k l) (expJet2Curve g gi hC p v Φ hv hΦcont h l) (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont k m) (expJet2Curve g gi hC p v Φ hv hΦcont h m) (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont k r) (expJet2Curve g gi hC p v Φ hv hΦcont h r) (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k r) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont l m) (expJet2Curve g gi hC p v Φ hv hΦcont h m) (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont l r) (expJet2Curve g gi hC p v Φ hv hΦcont h r) (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l r) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont m r) (expJet2Curve g gi hC p v Φ hv hΦcont h r) (expJet2Curve g gi hC p v Φ hv hΦcont h m) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) h m r) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont l m) (expJet2Curve g gi hC p v Φ hv hΦcont k m) (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont l r) (expJet2Curve g gi hC p v Φ hv hΦcont k r) (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l r) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont m r) (expJet2Curve g gi hC p v Φ hv hΦcont k r) (expJet2Curve g gi hC p v Φ hv hΦcont k m) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) k m r) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont m r) (expJet2Curve g gi hC p v Φ hv hΦcont l r) (expJet2Curve g gi hC p v Φ hv hΦcont l m) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) l m r) (expJet4Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont h k) (expJet2Curve g gi hC p v Φ hv hΦcont h l) (expJet2Curve g gi hC p v Φ hv hΦcont h m) (expJet2Curve g gi hC p v Φ hv hΦcont k l) (expJet2Curve g gi hC p v Φ hv hΦcont k m) (expJet2Curve g gi hC p v Φ hv hΦcont l m) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont k l) (expJet2Curve g gi hC p v Φ hv hΦcont h l) (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont k m) (expJet2Curve g gi hC p v Φ hv hΦcont h m) (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont l m) (expJet2Curve g gi hC p v Φ hv hΦcont h m) (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont l m) (expJet2Curve g gi hC p v Φ hv hΦcont k m) (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet3Curve_continuousOn g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont k l) (expJet2Curve g gi hC p v Φ hv hΦcont h l) (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l) (expJet3Curve_continuousOn g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont k m) (expJet2Curve g gi hC p v Φ hv hΦcont h m) (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m) (expJet3Curve_continuousOn g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont l m) (expJet2Curve g gi hC p v Φ hv hΦcont h m) (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m) (expJet3Curve_continuousOn g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont l m) (expJet2Curve g gi hC p v Φ hv hΦcont k m) (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m) h k l m) (expJet4Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont h k) (expJet2Curve g gi hC p v Φ hv hΦcont h l) (expJet2Curve g gi hC p v Φ hv hΦcont h r) (expJet2Curve g gi hC p v Φ hv hΦcont k l) (expJet2Curve g gi hC p v Φ hv hΦcont k r) (expJet2Curve g gi hC p v Φ hv hΦcont l r) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont k l) (expJet2Curve g gi hC p v Φ hv hΦcont h l) (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont k r) (expJet2Curve g gi hC p v Φ hv hΦcont h r) (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k r) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont l r) (expJet2Curve g gi hC p v Φ hv hΦcont h r) (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l r) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont l r) (expJet2Curve g gi hC p v Φ hv hΦcont k r) (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l r) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet3Curve_continuousOn g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont k l) (expJet2Curve g gi hC p v Φ hv hΦcont h l) (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l) (expJet3Curve_continuousOn g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont k r) (expJet2Curve g gi hC p v Φ hv hΦcont h r) (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k r) (expJet3Curve_continuousOn g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont l r) (expJet2Curve g gi hC p v Φ hv hΦcont h r) (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l r) (expJet3Curve_continuousOn g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont l r) (expJet2Curve g gi hC p v Φ hv hΦcont k r) (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l r) h k l r) (expJet4Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont h k) (expJet2Curve g gi hC p v Φ hv hΦcont h m) (expJet2Curve g gi hC p v Φ hv hΦcont h r) (expJet2Curve g gi hC p v Φ hv hΦcont k m) (expJet2Curve g gi hC p v Φ hv hΦcont k r) (expJet2Curve g gi hC p v Φ hv hΦcont m r) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont k m) (expJet2Curve g gi hC p v Φ hv hΦcont h m) (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont k r) (expJet2Curve g gi hC p v Φ hv hΦcont h r) (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k r) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont m r) (expJet2Curve g gi hC p v Φ hv hΦcont h r) (expJet2Curve g gi hC p v Φ hv hΦcont h m) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) h m r) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont m r) (expJet2Curve g gi hC p v Φ hv hΦcont k r) (expJet2Curve g gi hC p v Φ hv hΦcont k m) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) k m r) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet3Curve_continuousOn g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont k m) (expJet2Curve g gi hC p v Φ hv hΦcont h m) (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m) (expJet3Curve_continuousOn g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont k r) (expJet2Curve g gi hC p v Φ hv hΦcont h r) (expJet2Curve g gi hC p v Φ hv hΦcont h k) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k r) (expJet3Curve_continuousOn g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont m r) (expJet2Curve g gi hC p v Φ hv hΦcont h r) (expJet2Curve g gi hC p v Φ hv hΦcont h m) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) h m r) (expJet3Curve_continuousOn g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont m r) (expJet2Curve g gi hC p v Φ hv hΦcont k r) (expJet2Curve g gi hC p v Φ hv hΦcont k m) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) k m r) h k m r) (expJet4Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont h l) (expJet2Curve g gi hC p v Φ hv hΦcont h m) (expJet2Curve g gi hC p v Φ hv hΦcont h r) (expJet2Curve g gi hC p v Φ hv hΦcont l m) (expJet2Curve g gi hC p v Φ hv hΦcont l r) (expJet2Curve g gi hC p v Φ hv hΦcont m r) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont l m) (expJet2Curve g gi hC p v Φ hv hΦcont h m) (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont l r) (expJet2Curve g gi hC p v Φ hv hΦcont h r) (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l r) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont m r) (expJet2Curve g gi hC p v Φ hv hΦcont h r) (expJet2Curve g gi hC p v Φ hv hΦcont h m) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) h m r) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont m r) (expJet2Curve g gi hC p v Φ hv hΦcont l r) (expJet2Curve g gi hC p v Φ hv hΦcont l m) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) l m r) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet3Curve_continuousOn g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont l m) (expJet2Curve g gi hC p v Φ hv hΦcont h m) (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m) (expJet3Curve_continuousOn g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont l r) (expJet2Curve g gi hC p v Φ hv hΦcont h r) (expJet2Curve g gi hC p v Φ hv hΦcont h l) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l r) (expJet3Curve_continuousOn g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont m r) (expJet2Curve g gi hC p v Φ hv hΦcont h r) (expJet2Curve g gi hC p v Φ hv hΦcont h m) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) h m r) (expJet3Curve_continuousOn g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont m r) (expJet2Curve g gi hC p v Φ hv hΦcont l r) (expJet2Curve g gi hC p v Φ hv hΦcont l m) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) l m r) h l m r) (expJet4Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont k l) (expJet2Curve g gi hC p v Φ hv hΦcont k m) (expJet2Curve g gi hC p v Φ hv hΦcont k r) (expJet2Curve g gi hC p v Φ hv hΦcont l m) (expJet2Curve g gi hC p v Φ hv hΦcont l r) (expJet2Curve g gi hC p v Φ hv hΦcont m r) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont l m) (expJet2Curve g gi hC p v Φ hv hΦcont k m) (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont l r) (expJet2Curve g gi hC p v Φ hv hΦcont k r) (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l r) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont m r) (expJet2Curve g gi hC p v Φ hv hΦcont k r) (expJet2Curve g gi hC p v Φ hv hΦcont k m) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) k m r) (expJet3Curve g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont m r) (expJet2Curve g gi hC p v Φ hv hΦcont l r) (expJet2Curve g gi hC p v Φ hv hΦcont l m) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) l m r) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet3Curve_continuousOn g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont l m) (expJet2Curve g gi hC p v Φ hv hΦcont k m) (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m) (expJet3Curve_continuousOn g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont l r) (expJet2Curve g gi hC p v Φ hv hΦcont k r) (expJet2Curve g gi hC p v Φ hv hΦcont k l) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l r) (expJet3Curve_continuousOn g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont m r) (expJet2Curve g gi hC p v Φ hv hΦcont k r) (expJet2Curve g gi hC p v Φ hv hΦcont k m) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) k m r) (expJet3Curve_continuousOn g gi hC p v Φ (expJet2Curve g gi hC p v Φ hv hΦcont m r) (expJet2Curve g gi hC p v Φ hv hΦcont l r) (expJet2Curve g gi hC p v Φ hv hΦcont l m) hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) l m r) k l m r) h k l m r t)‖
        ≤ C₀ * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖ ^ 2 := by
  have hCst₀ := expConst_nonneg g gi hC p
  obtain ⟨Kf, hLipF⟩ := ((contDiff_geodesicField g gi hC).contDiffOn
      (s := Metric.closedBall ((p, 0) : Point n × Point n)
        (expConst g gi hC p * expRho g gi hC p))).exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  obtain ⟨Ldf, hLipDF⟩ := expJet_fderiv_lipschitzOnWith g gi hC p
  obtain ⟨Ld2f, hLipD2⟩ := expJet_fderiv2_lipschitzOnWith g gi hC p
  obtain ⟨Ld3f, hLipD3⟩ := expJet_fderiv3_lipschitzOnWith g gi hC p
  obtain ⟨Ld4f, hLipD4⟩ := expJet_fderiv4_lipschitzOnWith g gi hC p
  obtain ⟨Ld5f, hLipD5⟩ := expJet_fderiv5_lipschitzOnWith g gi hC p
  obtain ⟨Kstar, hKstar0, hKstaru⟩ := expJet_fderiv_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar2, hKstar20, hK2u⟩ := expJet_fderiv2_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar3, hKstar30, hK3u⟩ := expJet_fderiv3_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar4, hKstar40, hK4u⟩ := expJet_fderiv4_tube_bddAbove_unif g gi hC p
  obtain ⟨Kstar5, hKstar50, hK5u⟩ := expJet_fderiv5_tube_bddAbove_unif g gi hC p
  obtain ⟨Cd_fp, hCd_fp0, hFPU⟩ := expJet2FirstVar_residual_Icc_unif g gi hC p v Φ hv hΦ0 hΦcont hΦd
  obtain ⟨Cd_fq, hCd_fq0, hFQU⟩ := expJet3SecondVar_residual_Icc_unif g gi hC p v Φ hv hΦ0 hΦcont hΦd
  obtain ⟨Cd_fq4, hCd_fq40, hFQ4U⟩ := expJet4SecondVar_residual_Icc_unif g gi hC p v Φ hv hΦ0 hΦcont hΦd
  obtain ⟨Ce_2, hCe_20, hQL2U⟩ := expJet2_v_two_pt_Icc_unif g gi hC p v Φ hv hΦ0 hΦcont hΦd
  obtain ⟨Ce_3, hCe_30, hQL3U⟩ := expJet3Val_v_two_pt_Icc_unif g gi hC p v Φ hv hΦ0 hΦcont hΦd
  obtain ⟨Ce_4, hCe_40, hQL4U⟩ := expJet4Val_v_two_pt_Icc_unif g gi hC p v Φ hv hΦ0 hΦcont hΦd
  set eKf : ℝ := Real.exp (Kf : ℝ) with heKf
  have heKf0 : 0 ≤ eKf := (Real.exp_pos _).le
  set eKs : ℝ := Real.exp Kstar with heKs
  have heKs0 : 0 ≤ eKs := (Real.exp_pos _).le
  set M : ℝ := (Ldf : ℝ) with hMdef
  have hM0 : 0 ≤ M := Ldf.coe_nonneg
  set L2 : ℝ := (Ld2f : ℝ) with hL2def
  have hL2_0 : 0 ≤ L2 := Ld2f.coe_nonneg
  set L3 : ℝ := (Ld3f : ℝ) with hL3def
  have hL3_0 : 0 ≤ L3 := Ld3f.coe_nonneg
  set L4 : ℝ := (Ld4f : ℝ) with hL4def
  have hL4_0 : 0 ≤ L4 := Ld4f.coe_nonneg
  set L5 : ℝ := (Ld5f : ℝ) with hL5def
  have hL5_0 : 0 ≤ L5 := Ld5f.coe_nonneg
  set C2 : ℝ := M * eKf ^ 2 * eKs with hC2def
  have hC2_0 : 0 ≤ C2 := by rw [hC2def]; positivity
  set C3 : ℝ := M * eKf * eKs * eKs with hC3def
  have hC3_0 : 0 ≤ C3 := by rw [hC3def]; positivity
  set Cq2 : ℝ := Kstar2 * eKs ^ 2 * Real.exp Kstar with hCq2def
  have hCq20 : 0 ≤ Cq2 := by rw [hCq2def]; positivity
  set Ccr : ℝ := (Kstar3 * eKs ^ 3 + Kstar2 * eKs * Cq2 + Kstar2 * eKs * Cq2 + Kstar2 * eKs * Cq2)
      * Real.exp Kstar with hCcrdef
  have hCcr0 : 0 ≤ Ccr := by rw [hCcrdef]; positivity
  set Cq3 : ℝ := Ccr * (1 + 2 * expRho g gi hC p) with hCq3def
  have hCq30 : 0 ≤ Cq3 := by
    rw [hCq3def]; exact mul_nonneg hCcr0 (by linarith [(expRho_pos g gi hC p).le])
  have hCcr_le_Cq3 : Ccr ≤ Cq3 := by
    rw [hCq3def]; exact le_mul_of_one_le_right hCcr0 (by linarith [(expRho_pos g gi hC p).le])
  set VFq : ℝ := Cq2 + Cq2 + Cq3 with hVFqdef
  have hVFq0 : 0 ≤ VFq := by rw [hVFqdef]; exact add_nonneg (add_nonneg hCq20 hCq20) hCq30
  set Cd : ℝ := max (max Cd_fp Cd_fq) Cd_fq4 with hCddef
  have hCdfp_le : Cd_fp ≤ Cd := by rw [hCddef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hCdfq_le : Cd_fq ≤ Cd := by rw [hCddef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hCdfq4_le : Cd_fq4 ≤ Cd := by rw [hCddef]; exact le_max_right _ _
  have hCd0 : 0 ≤ Cd := le_trans hCd_fp0 hCdfp_le
  set Ce : ℝ := max (max Ce_2 Ce_3) Ce_4 with hCedef
  have hCe2_le : Ce_2 ≤ Ce := by rw [hCedef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hCe3_le : Ce_3 ≤ Ce := by rw [hCedef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hCe4_le : Ce_4 ≤ Ce := by rw [hCedef]; exact le_max_right _ _
  have hCe0 : 0 ≤ Ce := le_trans hCe_20 hCe2_le
  set Mc : ℝ := (Kstar4 * eKs ^ 4
      + Kstar3 * eKs ^ 2 * Cq2 + Kstar3 * eKs ^ 2 * Cq2 + Kstar3 * eKs ^ 2 * Cq2
      + Kstar3 * eKs ^ 2 * Cq2 + Kstar3 * eKs ^ 2 * Cq2 + Kstar3 * eKs ^ 2 * Cq2
      + Kstar2 * Cq2 ^ 2 + Kstar2 * Cq2 ^ 2 + Kstar2 * Cq2 ^ 2
      + Kstar2 * eKs * Cq3 + Kstar2 * eKs * Cq3 + Kstar2 * eKs * Cq3 + Kstar2 * eKs * Cq3)
      * Real.exp Kstar with hMcdef
  have hMc0 : 0 ≤ Mc := by rw [hMcdef]; positivity
  have hLipDF_M : LipschitzOnWith M.toNNReal (fderiv ℝ (geodesicField g gi))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hMdef, Real.toNNReal_coe]; exact hLipDF
  have hLipD2R : LipschitzOnWith L2.toNNReal (fderiv ℝ (fderiv ℝ (geodesicField g gi)))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hL2def, Real.toNNReal_coe]; exact hLipD2
  have hLipD3R : LipschitzOnWith L3.toNNReal
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hL3def, Real.toNNReal_coe]; exact hLipD3
  have hLipD4R : LipschitzOnWith L4.toNNReal
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hL4def, Real.toNNReal_coe]; exact hLipD4
  have hLipD5R : LipschitzOnWith L5.toNNReal
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))))
      (Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p)) := by
    rw [hL5def, Real.toNNReal_coe]; exact hLipD5
  have hKstarv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ Kstar := hKstaru v hv
  have hK2v : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)‖ ≤ Kstar2 := hK2u v hv
  have hK3v : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)‖ ≤ Kstar3 :=
    hK3u v hv
  have hK4v : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)‖
        ≤ Kstar4 := hK4u v hv
  have hK5v : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))
        (expTube g gi hC p v t)‖ ≤ Kstar5 := hK5u v hv
  have hΦnorm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t‖ ≤ eKs :=
    expJetFund_norm_le_exp g gi hC p v Φ Kstar hKstar0 hKstarv hΦ0 hΦd
  obtain ⟨hY0v, hYdv, hconfv⟩ := expTube_spec g gi hC p v hv
  have hmemv : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p v t ∈
      Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p) := by
    intro t ht; rw [Metric.mem_closedBall, dist_eq_norm]
    exact (hconfv t ht).trans (mul_le_mul_of_nonneg_left hv hCst₀)
  refine ⟨3*C2*Cq2^2*Kstar3 + 6*C2*Cq2*Kstar4*eKs^2 + 4*C2*Cq3*Kstar3*eKs + C2*Kstar2*Mc + C2*Kstar5*eKs^4 + 3*Ccr^2*Kstar2 + 6*Cd*Cq2*Kstar2 + 48*Cd*Cq2*Kstar3*eKs + 18*Cd*Cq3*Kstar2 + 3*Cd*Kstar2*VFq + 4*Cd*Kstar2*eKs + 6*Cd*Kstar3*eKs^2 + 16*Cd*Kstar4*eKs^3 + 6*C3^2*Cq2*Kstar3 + 6*C3^2*Kstar4*eKs^2 + 4*C3*Ce*Kstar2 + 12*C3*Ce*Kstar3*eKs + 12*C3*Cq2*Kstar4*eKs^2 + 4*C3*Cq3*Kstar3*eKs + 4*C3*Kstar5*eKs^4 + 6*Ce*Cq2*Kstar3*eKs + 4*Ce*Kstar3*eKs^2 + 6*Ce*Kstar4*eKs^3 + Ce*Kstar2*eKs + 3*Cq2^2*L3*eKf^2 + 6*Cq2*L4*eKf^2*eKs^2 + 4*Cq3*L3*eKf^2*eKs + L2*Mc*eKf^2 + L5*eKf^2*eKs^4, by positivity, ?_⟩
  intro r hvr Φ' hΦ'0 hΦ'cont hΦ'd h k l m
  set nr : ℝ := ‖r‖ with hnrdef
  have hnr0 : 0 ≤ nr := norm_nonneg r
  have hr_le : ‖r‖ ≤ 2 * expRho g gi hC p := by
    have hrr : ‖r‖ = ‖(v + r) - v‖ := by rw [add_sub_cancel_left]
    rw [hrr]
    calc ‖(v + r) - v‖ ≤ ‖v + r‖ + ‖v‖ := norm_sub_le _ _
      _ ≤ expRho g gi hC p + expRho g gi hC p := add_le_add hvr hv
      _ = 2 * expRho g gi hC p := by ring
  have hr_le1 : ‖r‖ ≤ 1 + 2 * expRho g gi hC p := hr_le.trans (by linarith)
  -- ── genuine curve abbreviations (pairs → triples → quads) ──
  set Qhk := expJet2Curve g gi hC p v Φ hv hΦcont h k
  set Qhl := expJet2Curve g gi hC p v Φ hv hΦcont h l
  set Qhm := expJet2Curve g gi hC p v Φ hv hΦcont h m
  set Qkl := expJet2Curve g gi hC p v Φ hv hΦcont k l
  set Qkm := expJet2Curve g gi hC p v Φ hv hΦcont k m
  set Qlm := expJet2Curve g gi hC p v Φ hv hΦcont l m
  set Qhr := expJet2Curve g gi hC p v Φ hv hΦcont h r
  set Qkr := expJet2Curve g gi hC p v Φ hv hΦcont k r
  set Qlr := expJet2Curve g gi hC p v Φ hv hΦcont l r
  set Qmr := expJet2Curve g gi hC p v Φ hv hΦcont m r
  set Qwhk := expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h k
  set Qwhl := expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h l
  set Qwhm := expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont h m
  set Qwkl := expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k l
  set Qwkm := expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont k m
  set Qwlm := expJet2Curve g gi hC p (v + r) Φ' hvr hΦ'cont l m
  set Qhkl := expJet3Curve g gi hC p v Φ Qkl Qhl Qhk hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l
  set Qhkm := expJet3Curve g gi hC p v Φ Qkm Qhm Qhk hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m
  set Qhlm := expJet3Curve g gi hC p v Φ Qlm Qhm Qhl hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m
  set Qklm := expJet3Curve g gi hC p v Φ Qlm Qkm Qkl hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m
  set Qhkr := expJet3Curve g gi hC p v Φ Qkr Qhr Qhk hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k r
  set Qhlr := expJet3Curve g gi hC p v Φ Qlr Qhr Qhl hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l r
  set Qhmr := expJet3Curve g gi hC p v Φ Qmr Qhr Qhm hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) h m r
  set Qklr := expJet3Curve g gi hC p v Φ Qlr Qkr Qkl hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l r
  set Qkmr := expJet3Curve g gi hC p v Φ Qmr Qkr Qkm hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) k m r
  set Qlmr := expJet3Curve g gi hC p v Φ Qmr Qlr Qlm hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) l m r
  set Qwhkl := expJet3Curve g gi hC p (v + r) Φ' Qwkl Qwhl Qwhk hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k l
  set Qwhkm := expJet3Curve g gi hC p (v + r) Φ' Qwkm Qwhm Qwhk hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k m
  set Qwhlm := expJet3Curve g gi hC p (v + r) Φ' Qwlm Qwhm Qwhl hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l) h l m
  set Qwklm := expJet3Curve g gi hC p (v + r) Φ' Qwlm Qwkm Qwkl hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l) k l m
  set Qhklm := expJet4Curve g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet3Curve_continuousOn g gi hC p v Φ Qkl Qhl Qhk hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l) (expJet3Curve_continuousOn g gi hC p v Φ Qkm Qhm Qhk hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m) (expJet3Curve_continuousOn g gi hC p v Φ Qlm Qhm Qhl hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m) (expJet3Curve_continuousOn g gi hC p v Φ Qlm Qkm Qkl hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m) h k l m
  set Qhklr := expJet4Curve g gi hC p v Φ Qhk Qhl Qhr Qkl Qkr Qlr Qhkl Qhkr Qhlr Qklr hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet3Curve_continuousOn g gi hC p v Φ Qkl Qhl Qhk hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l) (expJet3Curve_continuousOn g gi hC p v Φ Qkr Qhr Qhk hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k r) (expJet3Curve_continuousOn g gi hC p v Φ Qlr Qhr Qhl hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l r) (expJet3Curve_continuousOn g gi hC p v Φ Qlr Qkr Qkl hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l r) h k l r
  set Qhkmr := expJet4Curve g gi hC p v Φ Qhk Qhm Qhr Qkm Qkr Qmr Qhkm Qhkr Qhmr Qkmr hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet3Curve_continuousOn g gi hC p v Φ Qkm Qhm Qhk hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m) (expJet3Curve_continuousOn g gi hC p v Φ Qkr Qhr Qhk hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k r) (expJet3Curve_continuousOn g gi hC p v Φ Qmr Qhr Qhm hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) h m r) (expJet3Curve_continuousOn g gi hC p v Φ Qmr Qkr Qkm hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) k m r) h k m r
  set Qhlmr := expJet4Curve g gi hC p v Φ Qhl Qhm Qhr Qlm Qlr Qmr Qhlm Qhlr Qhmr Qlmr hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet3Curve_continuousOn g gi hC p v Φ Qlm Qhm Qhl hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m) (expJet3Curve_continuousOn g gi hC p v Φ Qlr Qhr Qhl hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l r) (expJet3Curve_continuousOn g gi hC p v Φ Qmr Qhr Qhm hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) h m r) (expJet3Curve_continuousOn g gi hC p v Φ Qmr Qlr Qlm hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) l m r) h l m r
  set Qklmr := expJet4Curve g gi hC p v Φ Qkl Qkm Qkr Qlm Qlr Qmr Qklm Qklr Qkmr Qlmr hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet3Curve_continuousOn g gi hC p v Φ Qlm Qkm Qkl hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m) (expJet3Curve_continuousOn g gi hC p v Φ Qlr Qkr Qkl hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l r) (expJet3Curve_continuousOn g gi hC p v Φ Qmr Qkr Qkm hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) k m r) (expJet3Curve_continuousOn g gi hC p v Φ Qmr Qlr Qlm hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) l m r) k l m r
  set Qw := expJet4Curve g gi hC p (v + r) Φ' Qwhk Qwhl Qwhm Qwkl Qwkm Qwlm Qwhkl Qwhkm Qwhlm Qwklm hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m) (expJet3Curve_continuousOn g gi hC p (v + r) Φ' Qwkl Qwhl Qwhk hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k l) (expJet3Curve_continuousOn g gi hC p (v + r) Φ' Qwkm Qwhm Qwhk hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k m) (expJet3Curve_continuousOn g gi hC p (v + r) Φ' Qwlm Qwhm Qwhl hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l) h l m) (expJet3Curve_continuousOn g gi hC p (v + r) Φ' Qwlm Qwkm Qwkl hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l) k l m) h k l m
  -- ── ODE/init data of the genuine curves ──
  obtain ⟨hQhk0, -, -, hQhkd⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h k).choose_spec
  obtain ⟨hQhl0, -, -, hQhld⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h l).choose_spec
  obtain ⟨hQhm0, -, -, hQhmd⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h m).choose_spec
  obtain ⟨hQkl0, -, -, hQkld⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont k l).choose_spec
  obtain ⟨hQkm0, -, -, hQkmd⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont k m).choose_spec
  obtain ⟨hQlm0, -, -, hQlmd⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont l m).choose_spec
  obtain ⟨hQhr0, -, -, hQhrd⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont h r).choose_spec
  obtain ⟨hQkr0, -, -, hQkrd⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont k r).choose_spec
  obtain ⟨hQlr0, -, -, hQlrd⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont l r).choose_spec
  obtain ⟨hQmr0, -, -, hQmrd⟩ := (expJet2Fund g gi hC p v Φ hv hΦcont m r).choose_spec
  obtain ⟨hQwhk0, -, -, hQwhkd⟩ := (expJet2Fund g gi hC p (v + r) Φ' hvr hΦ'cont h k).choose_spec
  obtain ⟨hQwhl0, -, -, hQwhld⟩ := (expJet2Fund g gi hC p (v + r) Φ' hvr hΦ'cont h l).choose_spec
  obtain ⟨hQwhm0, -, -, hQwhmd⟩ := (expJet2Fund g gi hC p (v + r) Φ' hvr hΦ'cont h m).choose_spec
  obtain ⟨hQwkl0, -, -, hQwkld⟩ := (expJet2Fund g gi hC p (v + r) Φ' hvr hΦ'cont k l).choose_spec
  obtain ⟨hQwkm0, -, -, hQwkmd⟩ := (expJet2Fund g gi hC p (v + r) Φ' hvr hΦ'cont k m).choose_spec
  obtain ⟨hQwlm0, -, -, hQwlmd⟩ := (expJet2Fund g gi hC p (v + r) Φ' hvr hΦ'cont l m).choose_spec
  obtain ⟨hQhkl0, -, -, hQhkld⟩ := (expJet3Fund g gi hC p v Φ Qkl Qhl Qhk hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k l).choose_spec
  obtain ⟨hQhkm0, -, -, hQhkmd⟩ := (expJet3Fund g gi hC p v Φ Qkm Qhm Qhk hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k m).choose_spec
  obtain ⟨hQhlm0, -, -, hQhlmd⟩ := (expJet3Fund g gi hC p v Φ Qlm Qhm Qhl hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l m).choose_spec
  obtain ⟨hQklm0, -, -, hQklmd⟩ := (expJet3Fund g gi hC p v Φ Qlm Qkm Qkl hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l m).choose_spec
  obtain ⟨hQhkr0, -, -, hQhkrd⟩ := (expJet3Fund g gi hC p v Φ Qkr Qhr Qhk hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h k) h k r).choose_spec
  obtain ⟨hQhlr0, -, -, hQhlrd⟩ := (expJet3Fund g gi hC p v Φ Qlr Qhr Qhl hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h l) h l r).choose_spec
  obtain ⟨hQhmr0, -, -, hQhmrd⟩ := (expJet3Fund g gi hC p v Φ Qmr Qhr Qhm hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont h m) h m r).choose_spec
  obtain ⟨hQklr0, -, -, hQklrd⟩ := (expJet3Fund g gi hC p v Φ Qlr Qkr Qkl hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k l) k l r).choose_spec
  obtain ⟨hQkmr0, -, -, hQkmrd⟩ := (expJet3Fund g gi hC p v Φ Qmr Qkr Qkm hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont k m) k m r).choose_spec
  obtain ⟨hQlmr0, -, -, hQlmrd⟩ := (expJet3Fund g gi hC p v Φ Qmr Qlr Qlm hv hΦcont (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont m r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l r) (expJet2Curve_continuousOn g gi hC p v Φ hv hΦcont l m) l m r).choose_spec
  obtain ⟨hQwhkl0, -, -, hQwhkld⟩ := (expJet3Fund g gi hC p (v + r) Φ' Qwkl Qwhl Qwhk hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k l).choose_spec
  obtain ⟨hQwhkm0, -, -, hQwhkmd⟩ := (expJet3Fund g gi hC p (v + r) Φ' Qwkm Qwhm Qwhk hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k m).choose_spec
  obtain ⟨hQwhlm0, -, -, hQwhlmd⟩ := (expJet3Fund g gi hC p (v + r) Φ' Qwlm Qwhm Qwhl hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l) h l m).choose_spec
  obtain ⟨hQwklm0, -, -, hQwklmd⟩ := (expJet3Fund g gi hC p (v + r) Φ' Qwlm Qwkm Qwkl hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l) k l m).choose_spec
  obtain ⟨hQw0, -, -, hQwd⟩ := (expJet4Fund g gi hC p (v + r) Φ' Qwhk Qwhl Qwhm Qwkl Qwkm Qwlm Qwhkl Qwhkm Qwhlm Qwklm hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m) (expJet3Curve_continuousOn g gi hC p (v + r) Φ' Qwkl Qwhl Qwhk hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k l) (expJet3Curve_continuousOn g gi hC p (v + r) Φ' Qwkm Qwhm Qwhk hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h k) h k m) (expJet3Curve_continuousOn g gi hC p (v + r) Φ' Qwlm Qwhm Qwhl hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont h l) h l m) (expJet3Curve_continuousOn g gi hC p (v + r) Φ' Qwlm Qwkm Qwkl hvr hΦ'cont (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont l m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k m) (expJet2Curve_continuousOn g gi hC p (v + r) Φ' hvr hΦ'cont k l) k l m) h k l m).choose_spec
  have hKstarw : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + r) t)‖ ≤ Kstar := hKstaru (v + r) hvr
  have hK2w : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p (v + r) t)‖ ≤ Kstar2 :=
    hK2u (v + r) hvr
  have hK3w : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p (v + r) t)‖ ≤ Kstar3 :=
    hK3u (v + r) hvr
  have hK4w : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p (v + r) t)‖
        ≤ Kstar4 := hK4u (v + r) hvr
  have hΦ'norm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ' t‖ ≤ eKs :=
    expJetFund_norm_le_exp g gi hC p (v + r) Φ' Kstar hKstar0 hKstarw hΦ'0 hΦ'd
  obtain ⟨hY0w, hYdw, hconfw⟩ := expTube_spec g gi hC p (v + r) hvr
  have hmemw : ∀ t ∈ Set.Icc (0 : ℝ) 1, expTube g gi hC p (v + r) t ∈
      Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p) := by
    intro t ht; rw [Metric.mem_closedBall, dist_eq_norm]
    exact (hconfw t ht).trans (mul_le_mul_of_nonneg_left hvr hCst₀)
  have hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expTube g gi hC p (v + r) t - expTube g gi hC p v t‖ ≤ nr * eKf := by
    have hIcc_Ioo : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∈ Set.Ioo (-2 : ℝ) 2 :=
      fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hdist0 : dist (expTube g gi hC p (v + r) 0) (expTube g gi hC p v 0) = nr := by
      rw [hY0w, hY0v, dist_eq_norm, Prod.mk_sub_mk, add_sub_cancel_left, sub_self, Prod.norm_def,
        norm_zero, max_eq_right (norm_nonneg _), hnrdef]
    have htwo := geodesic_twopoint_gronwall g gi
      (S := Metric.closedBall ((p, 0) : Point n × Point n) (expConst g gi hC p * expRho g gi hC p))
      (K := Kf) hLipF
      (fun t ht => hYdw t (hIcc_Ioo t ht)) (fun t ht => hYdv t (hIcc_Ioo t ht)) hmemw hmemv
    intro t ht
    have hh := htwo t ht
    rw [hdist0, dist_eq_norm] at hh
    refine hh.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _))
    calc (Kf : ℝ) * t ≤ (Kf : ℝ) * 1 := mul_le_mul_of_nonneg_left ht.2 (by positivity)
      _ = (Kf : ℝ) := mul_one _
  have htay : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + r) t)
          - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)
          - (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))
              (expTube g gi hC p (v + r) t - expTube g gi hC p v t)‖
        ≤ L2 * ‖expTube g gi hC p (v + r) t - expTube g gi hC p v t‖ ^ 2 :=
    fun t ht => geodesicField_DF_second_order_taylor g gi hC p L2 hL2_0 hLipD2R
      (expTube g gi hC p v t) (expTube g gi hC p (v + r) t) (hmemv t ht) (hmemw t ht)
  have hD2tay : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p (v + r) t)
          - fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)
          - (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))
              (expTube g gi hC p (v + r) t - expTube g gi hC p v t)‖
        ≤ L3 * ‖expTube g gi hC p (v + r) t - expTube g gi hC p v t‖ ^ 2 :=
    fun t ht => geodesicField_D2F_second_order_taylor g gi hC p L3 hL3_0 hLipD3R
      (expTube g gi hC p v t) (expTube g gi hC p (v + r) t) (hmemv t ht) (hmemw t ht)
  have hD3tay : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p (v + r) t)
          - fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)
          - (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))
              (expTube g gi hC p (v + r) t - expTube g gi hC p v t)‖
        ≤ L4 * ‖expTube g gi hC p (v + r) t - expTube g gi hC p v t‖ ^ 2 :=
    fun t ht => geodesicField_D3F_second_order_taylor g gi hC p L4 hL4_0 hLipD4R
      (expTube g gi hC p v t) (expTube g gi hC p (v + r) t) (hmemv t ht) (hmemw t ht)
  have hD4tay : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p (v + r) t)
          - fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)
          - (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))))
              (expTube g gi hC p v t))
              (expTube g gi hC p (v + r) t - expTube g gi hC p v t)‖
        ≤ L5 * ‖expTube g gi hC p (v + r) t - expTube g gi hC p v t‖ ^ 2 :=
    fun t ht => geodesicField_D4F_second_order_taylor g gi hC p L5 hL5_0 hLipD5R
      (expTube g gi hC p v t) (expTube g gi hC p (v + r) t) (hmemv t ht) (hmemw t ht)
  have hacc : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖expTube g gi hC p (v + r) t - expTube g gi hC p v t - Φ t (expJetIota r)‖ ≤ C2 * nr ^ 2 :=
    fun t ht => expTube_second_order_accuracy g gi hC p v r hvr hv M hM0 Kf Kstar hKstar0
      hLipF hLipDF_M hKstarv Φ hΦ0 hΦd t ht
  have htwopt : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Φ t - Φ' t‖ ≤ C3 * nr := by
    have hbase := expFund_two_pt_diff_Icc g gi hC p v (v + r) Kf Ldf Kstar hKstar0
      hLipF hLipDF hKstarv hKstarw hv hvr Φ Φ' hΦ0 hΦ'0 hΦd hΦ'd
    intro t ht
    have hb := hbase t ht
    rw [show v - (v + r) = -r by abel, norm_neg, ← hnrdef] at hb
    exact hb
  -- ── pair value bounds (Cq2) ──
  have hVhk : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhk t‖ ≤ Cq2 * ‖h‖ * ‖k‖ := by
    rw [hCq2def]
    exact expJet2Fund_value_bound_Icc g gi hC p v Φ h k Kstar Kstar2 eKs hKstar0 hKstar20 heKs0 hKstarv hK2v hΦnorm Qhk hQhk0 hQhkd
  have hVhl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhl t‖ ≤ Cq2 * ‖h‖ * ‖l‖ := by
    rw [hCq2def]
    exact expJet2Fund_value_bound_Icc g gi hC p v Φ h l Kstar Kstar2 eKs hKstar0 hKstar20 heKs0 hKstarv hK2v hΦnorm Qhl hQhl0 hQhld
  have hVhm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhm t‖ ≤ Cq2 * ‖h‖ * ‖m‖ := by
    rw [hCq2def]
    exact expJet2Fund_value_bound_Icc g gi hC p v Φ h m Kstar Kstar2 eKs hKstar0 hKstar20 heKs0 hKstarv hK2v hΦnorm Qhm hQhm0 hQhmd
  have hVkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkl t‖ ≤ Cq2 * ‖k‖ * ‖l‖ := by
    rw [hCq2def]
    exact expJet2Fund_value_bound_Icc g gi hC p v Φ k l Kstar Kstar2 eKs hKstar0 hKstar20 heKs0 hKstarv hK2v hΦnorm Qkl hQkl0 hQkld
  have hVkm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkm t‖ ≤ Cq2 * ‖k‖ * ‖m‖ := by
    rw [hCq2def]
    exact expJet2Fund_value_bound_Icc g gi hC p v Φ k m Kstar Kstar2 eKs hKstar0 hKstar20 heKs0 hKstarv hK2v hΦnorm Qkm hQkm0 hQkmd
  have hVlm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qlm t‖ ≤ Cq2 * ‖l‖ * ‖m‖ := by
    rw [hCq2def]
    exact expJet2Fund_value_bound_Icc g gi hC p v Φ l m Kstar Kstar2 eKs hKstar0 hKstar20 heKs0 hKstarv hK2v hΦnorm Qlm hQlm0 hQlmd
  have hVhr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhr t‖ ≤ Cq2 * ‖h‖ * ‖r‖ := by
    rw [hCq2def]
    exact expJet2Fund_value_bound_Icc g gi hC p v Φ h r Kstar Kstar2 eKs hKstar0 hKstar20 heKs0 hKstarv hK2v hΦnorm Qhr hQhr0 hQhrd
  have hVkr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkr t‖ ≤ Cq2 * ‖k‖ * ‖r‖ := by
    rw [hCq2def]
    exact expJet2Fund_value_bound_Icc g gi hC p v Φ k r Kstar Kstar2 eKs hKstar0 hKstar20 heKs0 hKstarv hK2v hΦnorm Qkr hQkr0 hQkrd
  have hVlr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qlr t‖ ≤ Cq2 * ‖l‖ * ‖r‖ := by
    rw [hCq2def]
    exact expJet2Fund_value_bound_Icc g gi hC p v Φ l r Kstar Kstar2 eKs hKstar0 hKstar20 heKs0 hKstarv hK2v hΦnorm Qlr hQlr0 hQlrd
  have hVmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qmr t‖ ≤ Cq2 * ‖m‖ * ‖r‖ := by
    rw [hCq2def]
    exact expJet2Fund_value_bound_Icc g gi hC p v Φ m r Kstar Kstar2 eKs hKstar0 hKstar20 heKs0 hKstarv hK2v hΦnorm Qmr hQmr0 hQmrd
  have hVwhk : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhk t‖ ≤ Cq2 * ‖h‖ * ‖k‖ := by
    rw [hCq2def]
    exact expJet2Fund_value_bound_Icc g gi hC p (v + r) Φ' h k Kstar Kstar2 eKs hKstar0 hKstar20 heKs0 hKstarw hK2w hΦ'norm Qwhk hQwhk0 hQwhkd
  have hVwhl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhl t‖ ≤ Cq2 * ‖h‖ * ‖l‖ := by
    rw [hCq2def]
    exact expJet2Fund_value_bound_Icc g gi hC p (v + r) Φ' h l Kstar Kstar2 eKs hKstar0 hKstar20 heKs0 hKstarw hK2w hΦ'norm Qwhl hQwhl0 hQwhld
  have hVwhm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhm t‖ ≤ Cq2 * ‖h‖ * ‖m‖ := by
    rw [hCq2def]
    exact expJet2Fund_value_bound_Icc g gi hC p (v + r) Φ' h m Kstar Kstar2 eKs hKstar0 hKstar20 heKs0 hKstarw hK2w hΦ'norm Qwhm hQwhm0 hQwhmd
  have hVwkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwkl t‖ ≤ Cq2 * ‖k‖ * ‖l‖ := by
    rw [hCq2def]
    exact expJet2Fund_value_bound_Icc g gi hC p (v + r) Φ' k l Kstar Kstar2 eKs hKstar0 hKstar20 heKs0 hKstarw hK2w hΦ'norm Qwkl hQwkl0 hQwkld
  have hVwkm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwkm t‖ ≤ Cq2 * ‖k‖ * ‖m‖ := by
    rw [hCq2def]
    exact expJet2Fund_value_bound_Icc g gi hC p (v + r) Φ' k m Kstar Kstar2 eKs hKstar0 hKstar20 heKs0 hKstarw hK2w hΦ'norm Qwkm hQwkm0 hQwkmd
  have hVwlm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwlm t‖ ≤ Cq2 * ‖l‖ * ‖m‖ := by
    rw [hCq2def]
    exact expJet2Fund_value_bound_Icc g gi hC p (v + r) Φ' l m Kstar Kstar2 eKs hKstar0 hKstar20 heKs0 hKstarw hK2w hΦ'norm Qwlm hQwlm0 hQwlmd
  -- ── triple value bounds (Cq3) ──
  have hVhkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkl t‖ ≤ Cq3 * ‖h‖ * ‖k‖ * ‖l‖ := by
    intro t ht
    have hb : ‖Qhkl t‖ ≤ Ccr * ‖h‖ * ‖k‖ * ‖l‖ :=
      (expJet3Fund_value_bound_Icc g gi hC p v Φ Qkl Qhl Qhk h k l Kstar Kstar3 Kstar2 eKs (Cq2 * ‖k‖ * ‖l‖) (Cq2 * ‖h‖ * ‖l‖) (Cq2 * ‖h‖ * ‖k‖) hKstar0 hKstar30 hKstar20 heKs0 hKstarv hK3v hK2v hΦnorm hVkl hVhl hVhk Qhkl hQhkl0 hQhkld t ht).trans (le_of_eq (by rw [hCcrdef]; ring))
    exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCcr_le_Cq3 (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _))
  have hVhkm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkm t‖ ≤ Cq3 * ‖h‖ * ‖k‖ * ‖m‖ := by
    intro t ht
    have hb : ‖Qhkm t‖ ≤ Ccr * ‖h‖ * ‖k‖ * ‖m‖ :=
      (expJet3Fund_value_bound_Icc g gi hC p v Φ Qkm Qhm Qhk h k m Kstar Kstar3 Kstar2 eKs (Cq2 * ‖k‖ * ‖m‖) (Cq2 * ‖h‖ * ‖m‖) (Cq2 * ‖h‖ * ‖k‖) hKstar0 hKstar30 hKstar20 heKs0 hKstarv hK3v hK2v hΦnorm hVkm hVhm hVhk Qhkm hQhkm0 hQhkmd t ht).trans (le_of_eq (by rw [hCcrdef]; ring))
    exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCcr_le_Cq3 (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _))
  have hVhlm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlm t‖ ≤ Cq3 * ‖h‖ * ‖l‖ * ‖m‖ := by
    intro t ht
    have hb : ‖Qhlm t‖ ≤ Ccr * ‖h‖ * ‖l‖ * ‖m‖ :=
      (expJet3Fund_value_bound_Icc g gi hC p v Φ Qlm Qhm Qhl h l m Kstar Kstar3 Kstar2 eKs (Cq2 * ‖l‖ * ‖m‖) (Cq2 * ‖h‖ * ‖m‖) (Cq2 * ‖h‖ * ‖l‖) hKstar0 hKstar30 hKstar20 heKs0 hKstarv hK3v hK2v hΦnorm hVlm hVhm hVhl Qhlm hQhlm0 hQhlmd t ht).trans (le_of_eq (by rw [hCcrdef]; ring))
    exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCcr_le_Cq3 (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _))
  have hVklm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklm t‖ ≤ Cq3 * ‖k‖ * ‖l‖ * ‖m‖ := by
    intro t ht
    have hb : ‖Qklm t‖ ≤ Ccr * ‖k‖ * ‖l‖ * ‖m‖ :=
      (expJet3Fund_value_bound_Icc g gi hC p v Φ Qlm Qkm Qkl k l m Kstar Kstar3 Kstar2 eKs (Cq2 * ‖l‖ * ‖m‖) (Cq2 * ‖k‖ * ‖m‖) (Cq2 * ‖k‖ * ‖l‖) hKstar0 hKstar30 hKstar20 heKs0 hKstarv hK3v hK2v hΦnorm hVlm hVkm hVkl Qklm hQklm0 hQklmd t ht).trans (le_of_eq (by rw [hCcrdef]; ring))
    exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCcr_le_Cq3 (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _))
  have hVwhkl : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhkl t‖ ≤ Cq3 * ‖h‖ * ‖k‖ * ‖l‖ := by
    intro t ht
    have hb : ‖Qwhkl t‖ ≤ Ccr * ‖h‖ * ‖k‖ * ‖l‖ :=
      (expJet3Fund_value_bound_Icc g gi hC p (v + r) Φ' Qwkl Qwhl Qwhk h k l Kstar Kstar3 Kstar2 eKs (Cq2 * ‖k‖ * ‖l‖) (Cq2 * ‖h‖ * ‖l‖) (Cq2 * ‖h‖ * ‖k‖) hKstar0 hKstar30 hKstar20 heKs0 hKstarw hK3w hK2w hΦ'norm hVwkl hVwhl hVwhk Qwhkl hQwhkl0 hQwhkld t ht).trans (le_of_eq (by rw [hCcrdef]; ring))
    exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCcr_le_Cq3 (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _))
  have hVwhkm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhkm t‖ ≤ Cq3 * ‖h‖ * ‖k‖ * ‖m‖ := by
    intro t ht
    have hb : ‖Qwhkm t‖ ≤ Ccr * ‖h‖ * ‖k‖ * ‖m‖ :=
      (expJet3Fund_value_bound_Icc g gi hC p (v + r) Φ' Qwkm Qwhm Qwhk h k m Kstar Kstar3 Kstar2 eKs (Cq2 * ‖k‖ * ‖m‖) (Cq2 * ‖h‖ * ‖m‖) (Cq2 * ‖h‖ * ‖k‖) hKstar0 hKstar30 hKstar20 heKs0 hKstarw hK3w hK2w hΦ'norm hVwkm hVwhm hVwhk Qwhkm hQwhkm0 hQwhkmd t ht).trans (le_of_eq (by rw [hCcrdef]; ring))
    exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCcr_le_Cq3 (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _))
  have hVwhlm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwhlm t‖ ≤ Cq3 * ‖h‖ * ‖l‖ * ‖m‖ := by
    intro t ht
    have hb : ‖Qwhlm t‖ ≤ Ccr * ‖h‖ * ‖l‖ * ‖m‖ :=
      (expJet3Fund_value_bound_Icc g gi hC p (v + r) Φ' Qwlm Qwhm Qwhl h l m Kstar Kstar3 Kstar2 eKs (Cq2 * ‖l‖ * ‖m‖) (Cq2 * ‖h‖ * ‖m‖) (Cq2 * ‖h‖ * ‖l‖) hKstar0 hKstar30 hKstar20 heKs0 hKstarw hK3w hK2w hΦ'norm hVwlm hVwhm hVwhl Qwhlm hQwhlm0 hQwhlmd t ht).trans (le_of_eq (by rw [hCcrdef]; ring))
    exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCcr_le_Cq3 (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _))
  have hVwklm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qwklm t‖ ≤ Cq3 * ‖k‖ * ‖l‖ * ‖m‖ := by
    intro t ht
    have hb : ‖Qwklm t‖ ≤ Ccr * ‖k‖ * ‖l‖ * ‖m‖ :=
      (expJet3Fund_value_bound_Icc g gi hC p (v + r) Φ' Qwlm Qwkm Qwkl k l m Kstar Kstar3 Kstar2 eKs (Cq2 * ‖l‖ * ‖m‖) (Cq2 * ‖k‖ * ‖m‖) (Cq2 * ‖k‖ * ‖l‖) hKstar0 hKstar30 hKstar20 heKs0 hKstarw hK3w hK2w hΦ'norm hVwlm hVwkm hVwkl Qwklm hQwklm0 hQwklmd t ht).trans (le_of_eq (by rw [hCcrdef]; ring))
    exact hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCcr_le_Cq3 (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _))
  -- ── r-triple value bounds (Ccr with ‖r‖, Cq3 absorbing ‖r‖) ──
  have hSQhkr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkr t‖ ≤ Ccr * ‖h‖ * ‖k‖ * ‖r‖ := by
    intro t ht
    refine (expJet3Fund_value_bound_Icc g gi hC p v Φ Qkr Qhr Qhk h k r Kstar Kstar3 Kstar2 eKs (Cq2 * ‖k‖ * ‖r‖) (Cq2 * ‖h‖ * ‖r‖) (Cq2 * ‖h‖ * ‖k‖) hKstar0 hKstar30 hKstar20 heKs0 hKstarv hK3v hK2v hΦnorm hVkr hVhr hVhk Qhkr hQhkr0 hQhkrd t ht).trans (le_of_eq ?_)
    rw [hCcrdef]; ring
  have hSQhlr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlr t‖ ≤ Ccr * ‖h‖ * ‖l‖ * ‖r‖ := by
    intro t ht
    refine (expJet3Fund_value_bound_Icc g gi hC p v Φ Qlr Qhr Qhl h l r Kstar Kstar3 Kstar2 eKs (Cq2 * ‖l‖ * ‖r‖) (Cq2 * ‖h‖ * ‖r‖) (Cq2 * ‖h‖ * ‖l‖) hKstar0 hKstar30 hKstar20 heKs0 hKstarv hK3v hK2v hΦnorm hVlr hVhr hVhl Qhlr hQhlr0 hQhlrd t ht).trans (le_of_eq ?_)
    rw [hCcrdef]; ring
  have hSQhmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhmr t‖ ≤ Ccr * ‖h‖ * ‖m‖ * ‖r‖ := by
    intro t ht
    refine (expJet3Fund_value_bound_Icc g gi hC p v Φ Qmr Qhr Qhm h m r Kstar Kstar3 Kstar2 eKs (Cq2 * ‖m‖ * ‖r‖) (Cq2 * ‖h‖ * ‖r‖) (Cq2 * ‖h‖ * ‖m‖) hKstar0 hKstar30 hKstar20 heKs0 hKstarv hK3v hK2v hΦnorm hVmr hVhr hVhm Qhmr hQhmr0 hQhmrd t ht).trans (le_of_eq ?_)
    rw [hCcrdef]; ring
  have hSQklr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklr t‖ ≤ Ccr * ‖k‖ * ‖l‖ * ‖r‖ := by
    intro t ht
    refine (expJet3Fund_value_bound_Icc g gi hC p v Φ Qlr Qkr Qkl k l r Kstar Kstar3 Kstar2 eKs (Cq2 * ‖l‖ * ‖r‖) (Cq2 * ‖k‖ * ‖r‖) (Cq2 * ‖k‖ * ‖l‖) hKstar0 hKstar30 hKstar20 heKs0 hKstarv hK3v hK2v hΦnorm hVlr hVkr hVkl Qklr hQklr0 hQklrd t ht).trans (le_of_eq ?_)
    rw [hCcrdef]; ring
  have hSQkmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkmr t‖ ≤ Ccr * ‖k‖ * ‖m‖ * ‖r‖ := by
    intro t ht
    refine (expJet3Fund_value_bound_Icc g gi hC p v Φ Qmr Qkr Qkm k m r Kstar Kstar3 Kstar2 eKs (Cq2 * ‖m‖ * ‖r‖) (Cq2 * ‖k‖ * ‖r‖) (Cq2 * ‖k‖ * ‖m‖) hKstar0 hKstar30 hKstar20 heKs0 hKstarv hK3v hK2v hΦnorm hVmr hVkr hVkm Qkmr hQkmr0 hQkmrd t ht).trans (le_of_eq ?_)
    rw [hCcrdef]; ring
  have hSQlmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qlmr t‖ ≤ Ccr * ‖l‖ * ‖m‖ * ‖r‖ := by
    intro t ht
    refine (expJet3Fund_value_bound_Icc g gi hC p v Φ Qmr Qlr Qlm l m r Kstar Kstar3 Kstar2 eKs (Cq2 * ‖m‖ * ‖r‖) (Cq2 * ‖l‖ * ‖r‖) (Cq2 * ‖l‖ * ‖m‖) hKstar0 hKstar30 hKstar20 heKs0 hKstarv hK3v hK2v hΦnorm hVmr hVlr hVlm Qlmr hQlmr0 hQlmrd t ht).trans (le_of_eq ?_)
    rw [hCcrdef]; ring
  have hVQhkr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhkr t‖ ≤ Cq3 * ‖h‖ * ‖k‖ := by
    intro t ht
    refine (hSQhkr t ht).trans ?_
    rw [hCq3def]
    have h1 : Ccr * ‖h‖ * ‖k‖ * ‖r‖ = (Ccr * ‖h‖ * ‖k‖) * ‖r‖ := by ring
    have h2 : Ccr * (1 + 2 * expRho g gi hC p) * ‖h‖ * ‖k‖ = (Ccr * ‖h‖ * ‖k‖) * (1 + 2 * expRho g gi hC p) := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left hr_le1 (mul_nonneg (mul_nonneg hCcr0 (norm_nonneg h)) (norm_nonneg k))
  have hVQhlr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhlr t‖ ≤ Cq3 * ‖h‖ * ‖l‖ := by
    intro t ht
    refine (hSQhlr t ht).trans ?_
    rw [hCq3def]
    have h1 : Ccr * ‖h‖ * ‖l‖ * ‖r‖ = (Ccr * ‖h‖ * ‖l‖) * ‖r‖ := by ring
    have h2 : Ccr * (1 + 2 * expRho g gi hC p) * ‖h‖ * ‖l‖ = (Ccr * ‖h‖ * ‖l‖) * (1 + 2 * expRho g gi hC p) := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left hr_le1 (mul_nonneg (mul_nonneg hCcr0 (norm_nonneg h)) (norm_nonneg l))
  have hVQhmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qhmr t‖ ≤ Cq3 * ‖h‖ * ‖m‖ := by
    intro t ht
    refine (hSQhmr t ht).trans ?_
    rw [hCq3def]
    have h1 : Ccr * ‖h‖ * ‖m‖ * ‖r‖ = (Ccr * ‖h‖ * ‖m‖) * ‖r‖ := by ring
    have h2 : Ccr * (1 + 2 * expRho g gi hC p) * ‖h‖ * ‖m‖ = (Ccr * ‖h‖ * ‖m‖) * (1 + 2 * expRho g gi hC p) := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left hr_le1 (mul_nonneg (mul_nonneg hCcr0 (norm_nonneg h)) (norm_nonneg m))
  have hVQklr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qklr t‖ ≤ Cq3 * ‖k‖ * ‖l‖ := by
    intro t ht
    refine (hSQklr t ht).trans ?_
    rw [hCq3def]
    have h1 : Ccr * ‖k‖ * ‖l‖ * ‖r‖ = (Ccr * ‖k‖ * ‖l‖) * ‖r‖ := by ring
    have h2 : Ccr * (1 + 2 * expRho g gi hC p) * ‖k‖ * ‖l‖ = (Ccr * ‖k‖ * ‖l‖) * (1 + 2 * expRho g gi hC p) := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left hr_le1 (mul_nonneg (mul_nonneg hCcr0 (norm_nonneg k)) (norm_nonneg l))
  have hVQkmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qkmr t‖ ≤ Cq3 * ‖k‖ * ‖m‖ := by
    intro t ht
    refine (hSQkmr t ht).trans ?_
    rw [hCq3def]
    have h1 : Ccr * ‖k‖ * ‖m‖ * ‖r‖ = (Ccr * ‖k‖ * ‖m‖) * ‖r‖ := by ring
    have h2 : Ccr * (1 + 2 * expRho g gi hC p) * ‖k‖ * ‖m‖ = (Ccr * ‖k‖ * ‖m‖) * (1 + 2 * expRho g gi hC p) := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left hr_le1 (mul_nonneg (mul_nonneg hCcr0 (norm_nonneg k)) (norm_nonneg m))
  have hVQlmr : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖Qlmr t‖ ≤ Cq3 * ‖l‖ * ‖m‖ := by
    intro t ht
    refine (hSQlmr t ht).trans ?_
    rw [hCq3def]
    have h1 : Ccr * ‖l‖ * ‖m‖ * ‖r‖ = (Ccr * ‖l‖ * ‖m‖) * ‖r‖ := by ring
    have h2 : Ccr * (1 + 2 * expRho g gi hC p) * ‖l‖ * ‖m‖ = (Ccr * ‖l‖ * ‖m‖) * (1 + 2 * expRho g gi hC p) := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left hr_le1 (mul_nonneg (mul_nonneg hCcr0 (norm_nonneg l)) (norm_nonneg m))
  -- ── first→second residuals (hFP) ──
  have hFPh : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Φ' t (expJetIota h) - Φ t (expJetIota h) - Qhr t‖ ≤ Cd * ‖h‖ * ‖r‖ ^ 2 := fun t ht =>
    (hFPU r hvr Φ' hΦ'0 hΦ'cont hΦ'd h t ht).trans (by gcongr)
  have hFPk : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Φ' t (expJetIota k) - Φ t (expJetIota k) - Qkr t‖ ≤ Cd * ‖k‖ * ‖r‖ ^ 2 := fun t ht =>
    (hFPU r hvr Φ' hΦ'0 hΦ'cont hΦ'd k t ht).trans (by gcongr)
  have hFPl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Φ' t (expJetIota l) - Φ t (expJetIota l) - Qlr t‖ ≤ Cd * ‖l‖ * ‖r‖ ^ 2 := fun t ht =>
    (hFPU r hvr Φ' hΦ'0 hΦ'cont hΦ'd l t ht).trans (by gcongr)
  have hFPm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Φ' t (expJetIota m) - Φ t (expJetIota m) - Qmr t‖ ≤ Cd * ‖m‖ * ‖r‖ ^ 2 := fun t ht =>
    (hFPU r hvr Φ' hΦ'0 hΦ'cont hΦ'd m t ht).trans (by gcongr)
  -- ── pair two-point (hQL, Ce) ──
  have hQLhk : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhk t - Qhk t‖ ≤ Ce * ‖h‖ * ‖k‖ * ‖r‖ := fun t ht =>
    (hQL2U r hvr Φ' hΦ'0 hΦ'cont hΦ'd h k t ht).trans (by gcongr)
  have hQLhl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhl t - Qhl t‖ ≤ Ce * ‖h‖ * ‖l‖ * ‖r‖ := fun t ht =>
    (hQL2U r hvr Φ' hΦ'0 hΦ'cont hΦ'd h l t ht).trans (by gcongr)
  have hQLhm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhm t - Qhm t‖ ≤ Ce * ‖h‖ * ‖m‖ * ‖r‖ := fun t ht =>
    (hQL2U r hvr Φ' hΦ'0 hΦ'cont hΦ'd h m t ht).trans (by gcongr)
  have hQLkl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwkl t - Qkl t‖ ≤ Ce * ‖k‖ * ‖l‖ * ‖r‖ := fun t ht =>
    (hQL2U r hvr Φ' hΦ'0 hΦ'cont hΦ'd k l t ht).trans (by gcongr)
  have hQLkm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwkm t - Qkm t‖ ≤ Ce * ‖k‖ * ‖m‖ * ‖r‖ := fun t ht =>
    (hQL2U r hvr Φ' hΦ'0 hΦ'cont hΦ'd k m t ht).trans (by gcongr)
  have hQLlm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwlm t - Qlm t‖ ≤ Ce * ‖l‖ * ‖m‖ * ‖r‖ := fun t ht =>
    (hQL2U r hvr Φ' hΦ'0 hΦ'cont hΦ'd l m t ht).trans (by gcongr)
  -- ── second→third residuals (hFQ) ──
  have hFQhk : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhk t - Qhk t - Qhkr t‖ ≤ Cd * ‖h‖ * ‖k‖ * ‖r‖ ^ 2 := fun t ht =>
    (hFQU r hvr Φ' hΦ'0 hΦ'cont hΦ'd h k t ht).trans (by gcongr)
  have hFQhl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhl t - Qhl t - Qhlr t‖ ≤ Cd * ‖h‖ * ‖l‖ * ‖r‖ ^ 2 := fun t ht =>
    (hFQU r hvr Φ' hΦ'0 hΦ'cont hΦ'd h l t ht).trans (by gcongr)
  have hFQhm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhm t - Qhm t - Qhmr t‖ ≤ Cd * ‖h‖ * ‖m‖ * ‖r‖ ^ 2 := fun t ht =>
    (hFQU r hvr Φ' hΦ'0 hΦ'cont hΦ'd h m t ht).trans (by gcongr)
  have hFQkl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwkl t - Qkl t - Qklr t‖ ≤ Cd * ‖k‖ * ‖l‖ * ‖r‖ ^ 2 := fun t ht =>
    (hFQU r hvr Φ' hΦ'0 hΦ'cont hΦ'd k l t ht).trans (by gcongr)
  have hFQkm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwkm t - Qkm t - Qkmr t‖ ≤ Cd * ‖k‖ * ‖m‖ * ‖r‖ ^ 2 := fun t ht =>
    (hFQU r hvr Φ' hΦ'0 hΦ'cont hΦ'd k m t ht).trans (by gcongr)
  have hFQlm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwlm t - Qlm t - Qlmr t‖ ≤ Cd * ‖l‖ * ‖m‖ * ‖r‖ ^ 2 := fun t ht =>
    (hFQU r hvr Φ' hΦ'0 hΦ'cont hΦ'd l m t ht).trans (by gcongr)
  -- ── triple two-point (hQL3, Ce) ──
  have hQL3klm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwklm t - Qklm t‖ ≤ Ce * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖ := fun t ht =>
    (hQL3U r hvr Φ' hΦ'0 hΦ'cont hΦ'd k l m t ht).trans (by gcongr)
  have hQL3hlm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhlm t - Qhlm t‖ ≤ Ce * ‖h‖ * ‖l‖ * ‖m‖ * ‖r‖ := fun t ht =>
    (hQL3U r hvr Φ' hΦ'0 hΦ'cont hΦ'd h l m t ht).trans (by gcongr)
  have hQL3hkm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhkm t - Qhkm t‖ ≤ Ce * ‖h‖ * ‖k‖ * ‖m‖ * ‖r‖ := fun t ht =>
    (hQL3U r hvr Φ' hΦ'0 hΦ'cont hΦ'd h k m t ht).trans (by gcongr)
  have hQL3hkl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhkl t - Qhkl t‖ ≤ Ce * ‖h‖ * ‖k‖ * ‖l‖ * ‖r‖ := fun t ht =>
    (hQL3U r hvr Φ' hΦ'0 hΦ'cont hΦ'd h k l t ht).trans (by gcongr)
  -- ── third→fourth residuals (hFQ3) ──
  have hFQ3klm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwklm t - Qklm t - Qklmr t‖ ≤ Cd * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖ ^ 2 := fun t ht =>
    (hFQ4U r hvr Φ' hΦ'0 hΦ'cont hΦ'd k l m t ht).trans (by gcongr)
  have hFQ3hlm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhlm t - Qhlm t - Qhlmr t‖ ≤ Cd * ‖h‖ * ‖l‖ * ‖m‖ * ‖r‖ ^ 2 := fun t ht =>
    (hFQ4U r hvr Φ' hΦ'0 hΦ'cont hΦ'd h l m t ht).trans (by gcongr)
  have hFQ3hkm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhkm t - Qhkm t - Qhkmr t‖ ≤ Cd * ‖h‖ * ‖k‖ * ‖m‖ * ‖r‖ ^ 2 := fun t ht =>
    (hFQ4U r hvr Φ' hΦ'0 hΦ'cont hΦ'd h k m t ht).trans (by gcongr)
  have hFQ3hkl : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qwhkl t - Qhkl t - Qhklr t‖ ≤ Cd * ‖h‖ * ‖k‖ * ‖l‖ * ‖r‖ ^ 2 := fun t ht =>
    (hFQ4U r hvr Φ' hΦ'0 hΦ'cont hΦ'd h k l t ht).trans (by gcongr)
  -- ── fourth-variation two-point (hQlipTop, Ce) ──
  have hQlipTop : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖Qw t - Qhklm t‖ ≤ Ce * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ * ‖r‖ := fun t ht =>
    (hQL4U r hvr Φ' hΦ'0 hΦ'cont hΦ'd h k l m t ht).trans (by gcongr)
  -- ── qw value bound + iota ──
  have hqwval := expJet4Fund_value_bound_Icc g gi hC p (v + r) Φ'
      Qwhk Qwhl Qwhm Qwkl Qwkm Qwlm Qwhkl Qwhkm Qwhlm Qwklm h k l m
      Kstar Kstar4 Kstar3 Kstar2 eKs
      (Cq2 * ‖h‖ * ‖k‖) (Cq2 * ‖h‖ * ‖l‖) (Cq2 * ‖h‖ * ‖m‖) (Cq2 * ‖k‖ * ‖l‖) (Cq2 * ‖k‖ * ‖m‖) (Cq2 * ‖l‖ * ‖m‖)
      (Cq3 * ‖h‖ * ‖k‖ * ‖l‖) (Cq3 * ‖h‖ * ‖k‖ * ‖m‖) (Cq3 * ‖h‖ * ‖l‖ * ‖m‖) (Cq3 * ‖k‖ * ‖l‖ * ‖m‖)
      hKstar0 hKstar40 hKstar30 hKstar20 heKs0 hKstarw hK4w hK3w hK2w hΦ'norm
      hVwhk hVwhl hVwhm hVwkl hVwkm hVwlm hVwhkl hVwhkm hVwhlm hVwklm Qw hQw0 hQwd
  have hιh : ‖expJetIota (n := n) h‖ ≤ ‖h‖ :=
    ((expJetIota (n := n)).le_opNorm h).trans (by
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg h))
  have hιk : ‖expJetIota (n := n) k‖ ≤ ‖k‖ :=
    ((expJetIota (n := n)).le_opNorm k).trans (by
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg k))
  have hιl : ‖expJetIota (n := n) l‖ ≤ ‖l‖ :=
    ((expJetIota (n := n)).le_opNorm l).trans (by
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg l))
  have hιm : ‖expJetIota (n := n) m‖ ≤ ‖m‖ :=
    ((expJetIota (n := n)).le_opNorm m).trans (by
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg m))
  have hιr : ‖expJetIota (n := n) r‖ ≤ ‖r‖ :=
    ((expJetIota (n := n)).le_opNorm r).trans (by
      simpa using mul_le_mul_of_nonneg_right expJetIota_opNorm_le (norm_nonneg r))
  intro t ht
  rw [expJet4Rhs_apply, expJet4Rhs_apply, expJet5Rhs_apply]
  have hd2n : ‖(fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t))‖ ≤ Kstar2 := hK2v t ht
  have hd3n : ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t))‖ ≤ Kstar3 := hK3v t ht
  have hd4n : ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t))‖ ≤ Kstar4 := hK4v t ht
  have hd5n : ‖(fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) (expTube g gi hC p v t))‖ ≤ Kstar5 := hK5v t ht
  have hsep2 : ‖(expTube g gi hC p (v + r) t) - (expTube g gi hC p v t)‖ ≤ nr * eKf := hsep t ht
  have htay2 := (htay t ht).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hsep2 2) hL2_0)
  have htay3 := (hD2tay t ht).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hsep2 2) hL3_0)
  have htay4 := (hD3tay t ht).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hsep2 2) hL4_0)
  have htay5 := (hD4tay t ht).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hsep2 2) hL5_0)
  have hacc0 : ‖(expTube g gi hC p (v + r) t) - (expTube g gi hC p v t) - (Φ t (expJetIota r))‖ ≤ C2 * nr ^ 2 := hacc t ht
  have hPrn : ‖(Φ t (expJetIota r))‖ ≤ eKs * nr := by
    exact clmApply_norm_le (Φ t) _ heKs0 (hΦnorm t ht) hιr
  have hcyc5 : (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) (expTube g gi hC p v t)) (Φ t (expJetIota r)) (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Φ t (expJetIota r)) :=
    fderiv5_geodesicField_symm_cyc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota r)) (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m))
  have hQa : (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Qhr t) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Qhr t) :=
    fderiv4_geodesicField_symm_cyc g gi hC (expTube g gi hC p v t) (Qhr t) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m))
  have hQb : (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Qkr t) (Φ t (expJetIota l)) (Φ t (expJetIota m)) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Qkr t) :=
    (fderiv4_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota h)) (Qkr t) (Φ t (expJetIota l)) (Φ t (expJetIota m))).trans
      (fderiv4_geodesicField_symm_cd g gi hC (expTube g gi hC p v t) (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Qkr t) (Φ t (expJetIota m)))
  have hQc : (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Qlr t) (Φ t (expJetIota m)) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota m)) (Qlr t) :=
    fderiv4_geodesicField_symm_cd g gi hC (expTube g gi hC p v t) (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Qlr t) (Φ t (expJetIota m))
  have hqwM4 : ‖Qw t‖ ≤ Mc * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖ :=
    (hqwval t ht).trans (le_of_eq (by rw [hMcdef]; ring))
  have hPhV : ‖(Φ t (expJetIota h))‖ ≤ eKs * ‖h‖ :=
    clmApply_norm_le (Φ t) _ heKs0 (hΦnorm t ht) hιh
  have hPkV : ‖(Φ t (expJetIota k))‖ ≤ eKs * ‖k‖ :=
    clmApply_norm_le (Φ t) _ heKs0 (hΦnorm t ht) hιk
  have hPlV : ‖(Φ t (expJetIota l))‖ ≤ eKs * ‖l‖ :=
    clmApply_norm_le (Φ t) _ heKs0 (hΦnorm t ht) hιl
  have hPmV : ‖(Φ t (expJetIota m))‖ ≤ eKs * ‖m‖ :=
    clmApply_norm_le (Φ t) _ heKs0 (hΦnorm t ht) hιm
  have hPhwV : ‖(Φ' t (expJetIota h))‖ ≤ eKs * ‖h‖ :=
    clmApply_norm_le (Φ' t) _ heKs0 (hΦ'norm t ht) hιh
  have hPkwV : ‖(Φ' t (expJetIota k))‖ ≤ eKs * ‖k‖ :=
    clmApply_norm_le (Φ' t) _ heKs0 (hΦ'norm t ht) hιk
  have hPlwV : ‖(Φ' t (expJetIota l))‖ ≤ eKs * ‖l‖ :=
    clmApply_norm_le (Φ' t) _ heKs0 (hΦ'norm t ht) hιl
  have hPmwV : ‖(Φ' t (expJetIota m))‖ ≤ eKs * ‖m‖ :=
    clmApply_norm_le (Φ' t) _ heKs0 (hΦ'norm t ht) hιm
  have hδH : ‖(Φ' t (expJetIota h)) - (Φ t (expJetIota h))‖ ≤ C3 * ‖h‖ * nr := by
    have he : (Φ' t (expJetIota h)) - (Φ t (expJetIota h)) = (Φ' t - Φ t) (expJetIota h) := by
      rw [ContinuousLinearMap.sub_apply]
    rw [he]
    calc ‖(Φ' t - Φ t) (expJetIota h)‖
        ≤ ‖Φ' t - Φ t‖ * ‖expJetIota (n := n) h‖ := (Φ' t - Φ t).le_opNorm _
      _ ≤ (C3 * nr) * ‖h‖ :=
          mul_le_mul (by rw [norm_sub_rev]; exact htwopt t ht) hιh (norm_nonneg _) (by positivity)
      _ = C3 * ‖h‖ * nr := by ring
  have hδK : ‖(Φ' t (expJetIota k)) - (Φ t (expJetIota k))‖ ≤ C3 * ‖k‖ * nr := by
    have he : (Φ' t (expJetIota k)) - (Φ t (expJetIota k)) = (Φ' t - Φ t) (expJetIota k) := by
      rw [ContinuousLinearMap.sub_apply]
    rw [he]
    calc ‖(Φ' t - Φ t) (expJetIota k)‖
        ≤ ‖Φ' t - Φ t‖ * ‖expJetIota (n := n) k‖ := (Φ' t - Φ t).le_opNorm _
      _ ≤ (C3 * nr) * ‖k‖ :=
          mul_le_mul (by rw [norm_sub_rev]; exact htwopt t ht) hιk (norm_nonneg _) (by positivity)
      _ = C3 * ‖k‖ * nr := by ring
  have hδL : ‖(Φ' t (expJetIota l)) - (Φ t (expJetIota l))‖ ≤ C3 * ‖l‖ * nr := by
    have he : (Φ' t (expJetIota l)) - (Φ t (expJetIota l)) = (Φ' t - Φ t) (expJetIota l) := by
      rw [ContinuousLinearMap.sub_apply]
    rw [he]
    calc ‖(Φ' t - Φ t) (expJetIota l)‖
        ≤ ‖Φ' t - Φ t‖ * ‖expJetIota (n := n) l‖ := (Φ' t - Φ t).le_opNorm _
      _ ≤ (C3 * nr) * ‖l‖ :=
          mul_le_mul (by rw [norm_sub_rev]; exact htwopt t ht) hιl (norm_nonneg _) (by positivity)
      _ = C3 * ‖l‖ * nr := by ring
  have hδM : ‖(Φ' t (expJetIota m)) - (Φ t (expJetIota m))‖ ≤ C3 * ‖m‖ * nr := by
    have he : (Φ' t (expJetIota m)) - (Φ t (expJetIota m)) = (Φ' t - Φ t) (expJetIota m) := by
      rw [ContinuousLinearMap.sub_apply]
    rw [he]
    calc ‖(Φ' t - Φ t) (expJetIota m)‖
        ≤ ‖Φ' t - Φ t‖ * ‖expJetIota (n := n) m‖ := (Φ' t - Φ t).le_opNorm _
      _ ≤ (C3 * nr) * ‖m‖ :=
          mul_le_mul (by rw [norm_sub_rev]; exact htwopt t ht) hιm (norm_nonneg _) (by positivity)
      _ = C3 * ‖m‖ * nr := by ring
  have hFQhkV : ‖Qwhk t - Qhk t - Qhkr t‖ ≤ VFq * ‖h‖ * ‖k‖ := by
    have hb : ‖Qwhk t - Qhk t - Qhkr t‖
        ≤ (Cq2 * ‖h‖ * ‖k‖ + Cq2 * ‖h‖ * ‖k‖) + Cq3 * ‖h‖ * ‖k‖ := by
      calc ‖Qwhk t - Qhk t - Qhkr t‖ ≤ ‖Qwhk t - Qhk t‖ + ‖Qhkr t‖ := norm_sub_le _ _
        _ ≤ (‖Qwhk t‖ + ‖Qhk t‖) + ‖Qhkr t‖ := add_le_add (norm_sub_le _ _) le_rfl
        _ ≤ (Cq2 * ‖h‖ * ‖k‖ + Cq2 * ‖h‖ * ‖k‖) + Cq3 * ‖h‖ * ‖k‖ :=
            add_le_add (add_le_add (hVwhk t ht) (hVhk t ht)) (hVQhkr t ht)
    refine hb.trans (le_of_eq ?_); rw [hVFqdef]; ring
  have hFQhlV : ‖Qwhl t - Qhl t - Qhlr t‖ ≤ VFq * ‖h‖ * ‖l‖ := by
    have hb : ‖Qwhl t - Qhl t - Qhlr t‖
        ≤ (Cq2 * ‖h‖ * ‖l‖ + Cq2 * ‖h‖ * ‖l‖) + Cq3 * ‖h‖ * ‖l‖ := by
      calc ‖Qwhl t - Qhl t - Qhlr t‖ ≤ ‖Qwhl t - Qhl t‖ + ‖Qhlr t‖ := norm_sub_le _ _
        _ ≤ (‖Qwhl t‖ + ‖Qhl t‖) + ‖Qhlr t‖ := add_le_add (norm_sub_le _ _) le_rfl
        _ ≤ (Cq2 * ‖h‖ * ‖l‖ + Cq2 * ‖h‖ * ‖l‖) + Cq3 * ‖h‖ * ‖l‖ :=
            add_le_add (add_le_add (hVwhl t ht) (hVhl t ht)) (hVQhlr t ht)
    refine hb.trans (le_of_eq ?_); rw [hVFqdef]; ring
  have hFQhmV : ‖Qwhm t - Qhm t - Qhmr t‖ ≤ VFq * ‖h‖ * ‖m‖ := by
    have hb : ‖Qwhm t - Qhm t - Qhmr t‖
        ≤ (Cq2 * ‖h‖ * ‖m‖ + Cq2 * ‖h‖ * ‖m‖) + Cq3 * ‖h‖ * ‖m‖ := by
      calc ‖Qwhm t - Qhm t - Qhmr t‖ ≤ ‖Qwhm t - Qhm t‖ + ‖Qhmr t‖ := norm_sub_le _ _
        _ ≤ (‖Qwhm t‖ + ‖Qhm t‖) + ‖Qhmr t‖ := add_le_add (norm_sub_le _ _) le_rfl
        _ ≤ (Cq2 * ‖h‖ * ‖m‖ + Cq2 * ‖h‖ * ‖m‖) + Cq3 * ‖h‖ * ‖m‖ :=
            add_le_add (add_le_add (hVwhm t ht) (hVhm t ht)) (hVQhmr t ht)
    refine hb.trans (le_of_eq ?_); rw [hVFqdef]; ring
  have hFQklV : ‖Qwkl t - Qkl t - Qklr t‖ ≤ VFq * ‖k‖ * ‖l‖ := by
    have hb : ‖Qwkl t - Qkl t - Qklr t‖
        ≤ (Cq2 * ‖k‖ * ‖l‖ + Cq2 * ‖k‖ * ‖l‖) + Cq3 * ‖k‖ * ‖l‖ := by
      calc ‖Qwkl t - Qkl t - Qklr t‖ ≤ ‖Qwkl t - Qkl t‖ + ‖Qklr t‖ := norm_sub_le _ _
        _ ≤ (‖Qwkl t‖ + ‖Qkl t‖) + ‖Qklr t‖ := add_le_add (norm_sub_le _ _) le_rfl
        _ ≤ (Cq2 * ‖k‖ * ‖l‖ + Cq2 * ‖k‖ * ‖l‖) + Cq3 * ‖k‖ * ‖l‖ :=
            add_le_add (add_le_add (hVwkl t ht) (hVkl t ht)) (hVQklr t ht)
    refine hb.trans (le_of_eq ?_); rw [hVFqdef]; ring
  have hFQkmV : ‖Qwkm t - Qkm t - Qkmr t‖ ≤ VFq * ‖k‖ * ‖m‖ := by
    have hb : ‖Qwkm t - Qkm t - Qkmr t‖
        ≤ (Cq2 * ‖k‖ * ‖m‖ + Cq2 * ‖k‖ * ‖m‖) + Cq3 * ‖k‖ * ‖m‖ := by
      calc ‖Qwkm t - Qkm t - Qkmr t‖ ≤ ‖Qwkm t - Qkm t‖ + ‖Qkmr t‖ := norm_sub_le _ _
        _ ≤ (‖Qwkm t‖ + ‖Qkm t‖) + ‖Qkmr t‖ := add_le_add (norm_sub_le _ _) le_rfl
        _ ≤ (Cq2 * ‖k‖ * ‖m‖ + Cq2 * ‖k‖ * ‖m‖) + Cq3 * ‖k‖ * ‖m‖ :=
            add_le_add (add_le_add (hVwkm t ht) (hVkm t ht)) (hVQkmr t ht)
    refine hb.trans (le_of_eq ?_); rw [hVFqdef]; ring
  have hFQlmV : ‖Qwlm t - Qlm t - Qlmr t‖ ≤ VFq * ‖l‖ * ‖m‖ := by
    have hb : ‖Qwlm t - Qlm t - Qlmr t‖
        ≤ (Cq2 * ‖l‖ * ‖m‖ + Cq2 * ‖l‖ * ‖m‖) + Cq3 * ‖l‖ * ‖m‖ := by
      calc ‖Qwlm t - Qlm t - Qlmr t‖ ≤ ‖Qwlm t - Qlm t‖ + ‖Qlmr t‖ := norm_sub_le _ _
        _ ≤ (‖Qwlm t‖ + ‖Qlm t‖) + ‖Qlmr t‖ := add_le_add (norm_sub_le _ _) le_rfl
        _ ≤ (Cq2 * ‖l‖ * ‖m‖ + Cq2 * ‖l‖ * ‖m‖) + Cq3 * ‖l‖ * ‖m‖ :=
            add_le_add (add_le_add (hVwlm t ht) (hVlm t ht)) (hVQlmr t ht)
    refine hb.trans (le_of_eq ?_); rw [hVFqdef]; ring
  have hs1 : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota m)) (Qhk t) (Qlr t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Qlr t) (Φ t (expJetIota m)) (Qhk t) :=
    (fderiv3_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota m)) (Qhk t) (Qlr t)).trans (fderiv3_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota m)) (Qlr t) (Qhk t))
  have hs2 : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota l)) (Qhk t) (Qmr t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota l)) (Qmr t) (Qhk t) :=
    fderiv3_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota l)) (Qhk t) (Qmr t)
  have hs3 : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota m)) (Qhl t) (Qkr t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Qkr t) (Φ t (expJetIota m)) (Qhl t) :=
    (fderiv3_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota m)) (Qhl t) (Qkr t)).trans (fderiv3_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota m)) (Qkr t) (Qhl t))
  have hs4 : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota k)) (Qhl t) (Qmr t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota k)) (Qmr t) (Qhl t) :=
    fderiv3_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota k)) (Qhl t) (Qmr t)
  have hs5 : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota l)) (Qhm t) (Qkr t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Qkr t) (Φ t (expJetIota l)) (Qhm t) :=
    (fderiv3_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota l)) (Qhm t) (Qkr t)).trans (fderiv3_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota l)) (Qkr t) (Qhm t))
  have hs6 : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota k)) (Qhm t) (Qlr t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota k)) (Qlr t) (Qhm t) :=
    fderiv3_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota k)) (Qhm t) (Qlr t)
  have hs7 : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota m)) (Qhr t) (Qkl t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Qhr t) (Φ t (expJetIota m)) (Qkl t) :=
    fderiv3_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota m)) (Qhr t) (Qkl t)
  have hs8 : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Qkl t) (Qmr t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Qmr t) (Qkl t) :=
    fderiv3_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota h)) (Qkl t) (Qmr t)
  have hs9 : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota l)) (Qhr t) (Qkm t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Qhr t) (Φ t (expJetIota l)) (Qkm t) :=
    fderiv3_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota l)) (Qhr t) (Qkm t)
  have hs10 : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Qkm t) (Qlr t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Qlr t) (Qkm t) :=
    fderiv3_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota h)) (Qkm t) (Qlr t)
  have hs11 : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota k)) (Qhr t) (Qlm t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Qhr t) (Φ t (expJetIota k)) (Qlm t) :=
    fderiv3_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota k)) (Qhr t) (Qlm t)
  have hs12 : (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qlmr t) (Qhk t) = (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qhk t) (Qlmr t) :=
    fderiv2_geodesicField_symm g gi hC (expTube g gi hC p v t) (Qlmr t) (Qhk t)
  have hs13 : (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qkmr t) (Qhl t) = (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qhl t) (Qkmr t) :=
    fderiv2_geodesicField_symm g gi hC (expTube g gi hC p v t) (Qkmr t) (Qhl t)
  have hs14 : (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qklr t) (Qhm t) = (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qhm t) (Qklr t) :=
    fderiv2_geodesicField_symm g gi hC (expTube g gi hC p v t) (Qklr t) (Qhm t)
  have hs15 : (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qklm t) (Qhr t) = (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qhr t) (Qklm t) :=
    fderiv2_geodesicField_symm g gi hC (expTube g gi hC p v t) (Qklm t) (Qhr t)
  have hs16 : (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qhlm t) (Qkr t) = (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qkr t) (Qhlm t) :=
    fderiv2_geodesicField_symm g gi hC (expTube g gi hC p v t) (Qhlm t) (Qkr t)
  have hs17 : (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qhkm t) (Qlr t) = (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qlr t) (Qhkm t) :=
    fderiv2_geodesicField_symm g gi hC (expTube g gi hC p v t) (Qhkm t) (Qlr t)
  have hs18 : (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qhkl t) (Qmr t) = (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (Qmr t) (Qhkl t) :=
    fderiv2_geodesicField_symm g gi hC (expTube g gi hC p v t) (Qhkl t) (Qmr t)
  have hcyc4_hk : (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota r)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Qhk t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Φ t (expJetIota r)) (Qhk t) :=
    (fderiv4_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota r)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Qhk t)).trans
      (fderiv4_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota l)) (Φ t (expJetIota r)) (Φ t (expJetIota m)) (Qhk t))
  have hcyc4_hl : (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota r)) (Φ t (expJetIota k)) (Φ t (expJetIota m)) (Qhl t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota k)) (Φ t (expJetIota m)) (Φ t (expJetIota r)) (Qhl t) :=
    (fderiv4_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota r)) (Φ t (expJetIota k)) (Φ t (expJetIota m)) (Qhl t)).trans
      (fderiv4_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota k)) (Φ t (expJetIota r)) (Φ t (expJetIota m)) (Qhl t))
  have hcyc4_hm : (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota r)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Qhm t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota r)) (Qhm t) :=
    (fderiv4_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota r)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Qhm t)).trans
      (fderiv4_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota k)) (Φ t (expJetIota r)) (Φ t (expJetIota l)) (Qhm t))
  have hcyc4_kl : (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota r)) (Φ t (expJetIota h)) (Φ t (expJetIota m)) (Qkl t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Φ t (expJetIota m)) (Φ t (expJetIota r)) (Qkl t) :=
    (fderiv4_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota r)) (Φ t (expJetIota h)) (Φ t (expJetIota m)) (Qkl t)).trans
      (fderiv4_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota h)) (Φ t (expJetIota r)) (Φ t (expJetIota m)) (Qkl t))
  have hcyc4_km : (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota r)) (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Qkm t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Φ t (expJetIota r)) (Qkm t) :=
    (fderiv4_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota r)) (Φ t (expJetIota h)) (Φ t (expJetIota l)) (Qkm t)).trans
      (fderiv4_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota h)) (Φ t (expJetIota r)) (Φ t (expJetIota l)) (Qkm t))
  have hcyc4_lm : (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota r)) (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Qlm t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota r)) (Qlm t) :=
    (fderiv4_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota r)) (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Qlm t)).trans
      (fderiv4_geodesicField_symm_bc g gi hC (expTube g gi hC p v t) (Φ t (expJetIota h)) (Φ t (expJetIota r)) (Φ t (expJetIota k)) (Qlm t))
  have hsA_klm : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota r)) (Φ t (expJetIota h)) (Qklm t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota h)) (Φ t (expJetIota r)) (Qklm t) :=
    fderiv3_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota r)) (Φ t (expJetIota h)) (Qklm t)
  have hsA_hlm : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota r)) (Φ t (expJetIota k)) (Qhlm t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota k)) (Φ t (expJetIota r)) (Qhlm t) :=
    fderiv3_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota r)) (Φ t (expJetIota k)) (Qhlm t)
  have hsA_hkm : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota r)) (Φ t (expJetIota l)) (Qhkm t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota l)) (Φ t (expJetIota r)) (Qhkm t) :=
    fderiv3_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota r)) (Φ t (expJetIota l)) (Qhkm t)
  have hsA_hkl : (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota r)) (Φ t (expJetIota m)) (Qhkl t) = (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (Φ t (expJetIota m)) (Φ t (expJetIota r)) (Qhkl t) :=
    fderiv3_geodesicField_symm_ab g gi hC (expTube g gi hC p v t) (Φ t (expJetIota r)) (Φ t (expJetIota m)) (Qhkl t)
  refine (remAssembly_dir
    (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (fderiv ℝ (geodesicField g gi) (expTube g gi hC p (v + r) t)) (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p v t)) (fderiv ℝ (fderiv ℝ (geodesicField g gi)) (expTube g gi hC p (v + r) t)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p v t)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))) (expTube g gi hC p (v + r) t)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p v t)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi)))) (expTube g gi hC p (v + r) t)) (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (geodesicField g gi))))) (expTube g gi hC p v t))
    (Qw t) (Φ t (expJetIota r)) (Φ t (expJetIota h)) (Φ t (expJetIota k)) (Φ t (expJetIota l)) (Φ t (expJetIota m)) (Φ' t (expJetIota h)) (Φ' t (expJetIota k)) (Φ' t (expJetIota l)) (Φ' t (expJetIota m)) (Qhk t) (Qhl t) (Qhm t) (Qkl t) (Qkm t) (Qlm t) (Qhr t) (Qkr t) (Qlr t) (Qmr t) (Qwhk t) (Qwhl t) (Qwhm t) (Qwkl t) (Qwkm t) (Qwlm t) (Qhkl t) (Qhkm t) (Qhlm t) (Qklm t) (Qhkr t) (Qhlr t) (Qhmr t) (Qklr t) (Qkmr t) (Qlmr t) (Qwhkl t) (Qwhkm t) (Qwhlm t) (Qwklm t) (Qhklm t) (Qhklr t) (Qhkmr t) (Qhlmr t) (Qklmr t) (expTube g gi hC p v t) (expTube g gi hC p (v + r) t)
    nr eKf eKs L2 L3 L4
    L5 C2 Kstar2 Kstar3 Kstar4 Kstar5
    (Mc * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖) (Ce * ‖h‖ * ‖k‖ * ‖l‖ * ‖m‖) (eKs * ‖h‖) (eKs * ‖k‖) (eKs * ‖l‖) (eKs * ‖m‖)
    (C3 * ‖h‖) (C3 * ‖k‖) (C3 * ‖l‖) (C3 * ‖m‖) (Cd * ‖h‖) (Cd * ‖k‖)
    (Cd * ‖l‖) (Cd * ‖m‖) (Cq2 * ‖h‖ * ‖k‖) (Cq2 * ‖h‖ * ‖l‖) (Cq2 * ‖h‖ * ‖m‖) (Cq2 * ‖k‖ * ‖l‖)
    (Cq2 * ‖k‖ * ‖m‖) (Cq2 * ‖l‖ * ‖m‖) (Ce * ‖h‖ * ‖k‖) (Ce * ‖h‖ * ‖l‖) (Ce * ‖h‖ * ‖m‖) (Ce * ‖k‖ * ‖l‖)
    (Ce * ‖k‖ * ‖m‖) (Ce * ‖l‖ * ‖m‖) (Cd * ‖h‖ * ‖k‖) (Cd * ‖h‖ * ‖l‖) (Cd * ‖h‖ * ‖m‖) (Cd * ‖k‖ * ‖l‖)
    (Cd * ‖k‖ * ‖m‖) (Cd * ‖l‖ * ‖m‖) (Cq3 * ‖h‖ * ‖k‖) (Cq3 * ‖h‖ * ‖l‖) (Cq3 * ‖h‖ * ‖m‖) (Cq3 * ‖k‖ * ‖l‖)
    (Cq3 * ‖k‖ * ‖m‖) (Cq3 * ‖l‖ * ‖m‖) (Ccr * ‖h‖ * ‖k‖) (Ccr * ‖h‖ * ‖l‖) (Ccr * ‖h‖ * ‖m‖) (Ccr * ‖k‖ * ‖l‖)
    (Ccr * ‖k‖ * ‖m‖) (Ccr * ‖l‖ * ‖m‖) (VFq * ‖h‖ * ‖k‖) (VFq * ‖h‖ * ‖l‖) (VFq * ‖h‖ * ‖m‖) (VFq * ‖k‖ * ‖l‖)
    (VFq * ‖k‖ * ‖m‖) (VFq * ‖l‖ * ‖m‖) (Cq3 * ‖k‖ * ‖l‖ * ‖m‖) (Cq3 * ‖h‖ * ‖l‖ * ‖m‖) (Cq3 * ‖h‖ * ‖k‖ * ‖m‖) (Cq3 * ‖h‖ * ‖k‖ * ‖l‖)
    (Ce * ‖k‖ * ‖l‖ * ‖m‖) (Ce * ‖h‖ * ‖l‖ * ‖m‖) (Ce * ‖h‖ * ‖k‖ * ‖m‖) (Ce * ‖h‖ * ‖k‖ * ‖l‖) (Cd * ‖k‖ * ‖l‖ * ‖m‖) (Cd * ‖h‖ * ‖l‖ * ‖m‖)
    (Cd * ‖h‖ * ‖k‖ * ‖m‖) (Cd * ‖h‖ * ‖k‖ * ‖l‖)
    hnr0 heKf0 heKs0 hL2_0
    hL3_0 hL4_0 hL5_0 hC2_0
    hKstar20 hKstar30 hKstar40 hKstar50
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hMc0 (norm_nonneg h)) (norm_nonneg k)) (norm_nonneg l)) (norm_nonneg m)) (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCe0 (norm_nonneg h)) (norm_nonneg k)) (norm_nonneg l)) (norm_nonneg m)) (mul_nonneg heKs0 (norm_nonneg h)) (mul_nonneg heKs0 (norm_nonneg k))
    (mul_nonneg heKs0 (norm_nonneg l)) (mul_nonneg heKs0 (norm_nonneg m)) (mul_nonneg hC3_0 (norm_nonneg h)) (mul_nonneg hC3_0 (norm_nonneg k))
    (mul_nonneg hC3_0 (norm_nonneg l)) (mul_nonneg hC3_0 (norm_nonneg m)) (mul_nonneg hCd0 (norm_nonneg h)) (mul_nonneg hCd0 (norm_nonneg k))
    (mul_nonneg hCd0 (norm_nonneg l)) (mul_nonneg hCd0 (norm_nonneg m)) (mul_nonneg (mul_nonneg hCq20 (norm_nonneg h)) (norm_nonneg k)) (mul_nonneg (mul_nonneg hCq20 (norm_nonneg h)) (norm_nonneg l))
    (mul_nonneg (mul_nonneg hCq20 (norm_nonneg h)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hCq20 (norm_nonneg k)) (norm_nonneg l)) (mul_nonneg (mul_nonneg hCq20 (norm_nonneg k)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hCq20 (norm_nonneg l)) (norm_nonneg m))
    (mul_nonneg (mul_nonneg hCe0 (norm_nonneg h)) (norm_nonneg k)) (mul_nonneg (mul_nonneg hCe0 (norm_nonneg h)) (norm_nonneg l)) (mul_nonneg (mul_nonneg hCe0 (norm_nonneg h)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hCe0 (norm_nonneg k)) (norm_nonneg l))
    (mul_nonneg (mul_nonneg hCe0 (norm_nonneg k)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hCe0 (norm_nonneg l)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hCd0 (norm_nonneg h)) (norm_nonneg k)) (mul_nonneg (mul_nonneg hCd0 (norm_nonneg h)) (norm_nonneg l))
    (mul_nonneg (mul_nonneg hCd0 (norm_nonneg h)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hCd0 (norm_nonneg k)) (norm_nonneg l)) (mul_nonneg (mul_nonneg hCd0 (norm_nonneg k)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hCd0 (norm_nonneg l)) (norm_nonneg m))
    (mul_nonneg (mul_nonneg hCq30 (norm_nonneg h)) (norm_nonneg k)) (mul_nonneg (mul_nonneg hCq30 (norm_nonneg h)) (norm_nonneg l)) (mul_nonneg (mul_nonneg hCq30 (norm_nonneg h)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hCq30 (norm_nonneg k)) (norm_nonneg l))
    (mul_nonneg (mul_nonneg hCq30 (norm_nonneg k)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hCq30 (norm_nonneg l)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hCcr0 (norm_nonneg h)) (norm_nonneg k)) (mul_nonneg (mul_nonneg hCcr0 (norm_nonneg h)) (norm_nonneg l))
    (mul_nonneg (mul_nonneg hCcr0 (norm_nonneg h)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hCcr0 (norm_nonneg k)) (norm_nonneg l)) (mul_nonneg (mul_nonneg hCcr0 (norm_nonneg k)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hCcr0 (norm_nonneg l)) (norm_nonneg m))
    (mul_nonneg (mul_nonneg hVFq0 (norm_nonneg h)) (norm_nonneg k)) (mul_nonneg (mul_nonneg hVFq0 (norm_nonneg h)) (norm_nonneg l)) (mul_nonneg (mul_nonneg hVFq0 (norm_nonneg h)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hVFq0 (norm_nonneg k)) (norm_nonneg l))
    (mul_nonneg (mul_nonneg hVFq0 (norm_nonneg k)) (norm_nonneg m)) (mul_nonneg (mul_nonneg hVFq0 (norm_nonneg l)) (norm_nonneg m)) (mul_nonneg (mul_nonneg (mul_nonneg hCq30 (norm_nonneg k)) (norm_nonneg l)) (norm_nonneg m)) (mul_nonneg (mul_nonneg (mul_nonneg hCq30 (norm_nonneg h)) (norm_nonneg l)) (norm_nonneg m))
    (mul_nonneg (mul_nonneg (mul_nonneg hCq30 (norm_nonneg h)) (norm_nonneg k)) (norm_nonneg m)) (mul_nonneg (mul_nonneg (mul_nonneg hCq30 (norm_nonneg h)) (norm_nonneg k)) (norm_nonneg l)) (mul_nonneg (mul_nonneg (mul_nonneg hCe0 (norm_nonneg k)) (norm_nonneg l)) (norm_nonneg m)) (mul_nonneg (mul_nonneg (mul_nonneg hCe0 (norm_nonneg h)) (norm_nonneg l)) (norm_nonneg m))
    (mul_nonneg (mul_nonneg (mul_nonneg hCe0 (norm_nonneg h)) (norm_nonneg k)) (norm_nonneg m)) (mul_nonneg (mul_nonneg (mul_nonneg hCe0 (norm_nonneg h)) (norm_nonneg k)) (norm_nonneg l)) (mul_nonneg (mul_nonneg (mul_nonneg hCd0 (norm_nonneg k)) (norm_nonneg l)) (norm_nonneg m)) (mul_nonneg (mul_nonneg (mul_nonneg hCd0 (norm_nonneg h)) (norm_nonneg l)) (norm_nonneg m))
    (mul_nonneg (mul_nonneg (mul_nonneg hCd0 (norm_nonneg h)) (norm_nonneg k)) (norm_nonneg m)) (mul_nonneg (mul_nonneg (mul_nonneg hCd0 (norm_nonneg h)) (norm_nonneg k)) (norm_nonneg l))
    htay2 htay3 htay4 htay5
    hacc0 hPrn hd2n hd3n
    hd4n hd5n hqwM4 (hQlipTop t ht)
    hPhV hPkV hPlV hPmV
    hPhwV hPkwV hPlwV hPmwV
    hδH hδK hδL hδM
    (hFPh t ht) (hFPk t ht) (hFPl t ht) (hFPm t ht)
    (hVhk t ht) (hVhl t ht) (hVhm t ht) (hVkl t ht)
    (hVkm t ht) (hVlm t ht) (hVwhk t ht) (hVwhl t ht)
    (hVwhm t ht) (hVwkl t ht) (hVwkm t ht) (hVwlm t ht)
    (hQLhk t ht) (hQLhl t ht) (hQLhm t ht) (hQLkl t ht)
    (hQLkm t ht) (hQLlm t ht) (hFQhk t ht) (hFQhl t ht)
    (hFQhm t ht) (hFQkl t ht) (hFQkm t ht) (hFQlm t ht)
    (hVQhkr t ht) (hVQhlr t ht) (hVQhmr t ht) (hVQklr t ht)
    (hVQkmr t ht) (hVQlmr t ht) (hSQhkr t ht) (hSQhlr t ht)
    (hSQhmr t ht) (hSQklr t ht) (hSQkmr t ht) (hSQlmr t ht)
    hFQhkV hFQhlV hFQhmV hFQklV
    hFQkmV hFQlmV (hVklm t ht) (hVhlm t ht)
    (hVhkm t ht) (hVhkl t ht) (hVwklm t ht) (hVwhlm t ht)
    (hVwhkm t ht) (hVwhkl t ht) (hQL3klm t ht) (hQL3hlm t ht)
    (hQL3hkm t ht) (hQL3hkl t ht) (hFQ3klm t ht) (hFQ3hlm t ht)
    (hFQ3hkm t ht) (hFQ3hkl t ht)
    hs1 hs2 hs3 hs4 hs5 hs6
    hs7 hs8 hs9 hs10 hs11 hs12
    hs13 hs14 hs15 hs16 hs17 hs18
    hcyc5 hQa hQb hQc hcyc4_hk hcyc4_hl
    hcyc4_hm hcyc4_kl hcyc4_km hcyc4_lm hsA_klm hsA_hlm
    hsA_hkm hsA_hkl).trans ?_
  rw [factor_hklm eKf eKs L2 L3 L4 L5 C2 Kstar2 Kstar3 Kstar4 Kstar5 C3 Cd Cq2 Cq3 Ce Ccr VFq Mc Ce ‖h‖ ‖k‖ ‖l‖ ‖m‖]
  exact le_of_eq (by ring)

end QIQTH.ExpMap
