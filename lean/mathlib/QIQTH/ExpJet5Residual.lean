/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet5Prereq

/-!
# Jet_5 parameter-residual ODE and its Groenwall endpoint bound -- rung J5-5a

Brick (a) of J5-5 of the JET-5 TOWER campaign: the order-5 parameter quadratic-remainder residual,
a FAITHFUL MIRROR -- one Frechet-derivative order higher -- of the landed Jet_4 residual bricks
`expJet4_residual_hasDerivWithinAt` / `expJet4_residual_bound` (`ExpJet4Residual.lean`).

With `Qv`,`Qw` the order-4 (fourth-variation) fundamental solutions (source `expJet4Rhs`) for base
points `v` and `w = v + m`, and `R` the order-5 (fifth-variation) solution (source `expJet5Rhs`) for
base `v`, the residual `S(t) = Qw(t) - Qv(t) - R(t)` solves, on `[0,1]`, the inhomogeneous linear ODE

  `S'(t) = DF(Y_v t)(S t) + rho(t)`,
  `rho(t) = [DF(Y_w t) - DF(Y_v t)](Qw t) + (Theta4_w(t) - Theta4_v(t) - Theta5_v(t))`,

with `S(0) = 0`.  Feeding this into the vector Groenwall `gronwall_vec_residual` gives the endpoint
bound `||Qw 1 - Qv 1 - R 1|| <= rho * e^{Kstar}`.

## Honest firewall (binding)

Brick (a) of J5-5 ONLY.  `expJet5_residual_bound` reduces the residual estimate to the single
`[0,1]`-uniform obligation `||rho(t)|| <= rho` (carried honestly as the explicit hypothesis `hr`,
exactly as in the Jet_4 mirror), plus the tube Jacobi bound `Kstar`.  The quadratic sharpening
`rho = C*||m||^2` is brick (b) (`expJet4SecondVar_residual_Icc_unif` mirror) -- NOT proven here.
This file does NOT prove `expMap_fderiv4_hasFDerivAt`, does NOT reach `exp in C^5`, `kappa = 1/6`, or
`a_1 = R/6` (CONDITIONAL).
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxSynthPendingDepth 5
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 2000000

variable {n : ℕ}

/-- **The Jet_5 parameter-residual ODE identity** (mirror of `expJet4_residual_hasDerivWithinAt`,
    one Frechet-derivative order higher).  With `Qv`,`Qw` the order-4 fundamental solutions (source
    `expJet4Rhs`) for base points `v`,`w`, and `R` the order-5 solution (source `expJet5Rhs`) for
    base `v`, the residual `S(t) = Qw(t) - Qv(t) - R(t)` obeys, on `[0,1]`,
    `S'(t) = DF(Y_v t)(S t) + ([DF(Y_w t) - DF(Y_v t)](Qw t) + (Theta4_w - Theta4_v - Theta5_v))`.

    Proof (mirror of the Jet_4 version): `Qw`,`Qv`,`R` solve their ODEs; `HasDerivWithinAt.sub` twice
    gives the natural difference derivative; `map_sub` + `ContinuousLinearMap.sub_apply` + `abel`
    regroup it into the `DF(Y_v t)(S) + rho` form. -/
theorem expJet5_residual_hasDerivWithinAt
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v w : Point n)
    (Φ Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qv Qw : ℝ → (Point n × Point n))
    (Qvhk Qvhl Qvhm Qvkl Qvkm Qvlm Qvhkl Qvhkm Qvhlm Qvklm : ℝ → (Point n × Point n))
    (Qwhk Qwhl Qwhm Qwkl Qwkm Qwlm Qwhkl Qwhkm Qwhlm Qwklm : ℝ → (Point n × Point n))
    (Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr R : ℝ → (Point n × Point n)) (h k l m r : Point n)
    (hQvd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Qv
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qv t)
           + expJet4Rhs g gi hC p v Φ Qvhk Qvhl Qvhm Qvkl Qvkm Qvlm Qvhkl Qvhkm Qvhlm Qvklm h k l m t) (Set.Icc (0 : ℝ) 1) t)
    (hQwd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Qw
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qw t)
           + expJet4Rhs g gi hC p w Φ' Qwhk Qwhl Qwhm Qwkl Qwkm Qwlm Qwhkl Qwhkm Qwhlm Qwklm h k l m t) (Set.Icc (0 : ℝ) 1) t)
    (hRd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt R
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R t)
           + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t) (Set.Icc (0 : ℝ) 1) t)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun s => Qw s - Qv s - R s)
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qw t - Qv t - R t)
        + (((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t))
             - (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))) (Qw t)
           + (expJet4Rhs g gi hC p w Φ' Qwhk Qwhl Qwhm Qwkl Qwkm Qwlm Qwhkl Qwhkm Qwhlm Qwklm h k l m t
              - expJet4Rhs g gi hC p v Φ Qvhk Qvhl Qvhm Qvkl Qvkm Qvlm Qvhkl Qvhkm Qvhlm Qvklm h k l m t
              - expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t)))
      (Set.Icc (0 : ℝ) 1) t := by
  have hcomb := ((hQwd t ht).sub (hQvd t ht)).sub (hRd t ht)
  have heq :
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qw t - Qv t - R t)
        + (((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t))
             - (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))) (Qw t)
           + (expJet4Rhs g gi hC p w Φ' Qwhk Qwhl Qwhm Qwkl Qwkm Qwlm Qwhkl Qwhkm Qwhlm Qwklm h k l m t
              - expJet4Rhs g gi hC p v Φ Qvhk Qvhl Qvhm Qvkl Qvkm Qvlm Qvhkl Qvhkm Qvhlm Qvklm h k l m t
              - expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t)))
      = (((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t))) (Qw t)
            + expJet4Rhs g gi hC p w Φ' Qwhk Qwhl Qwhm Qwkl Qwkm Qwlm Qwhkl Qwhkm Qwhlm Qwklm h k l m t)
          - (((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))) (Qv t)
             + expJet4Rhs g gi hC p v Φ Qvhk Qvhl Qvhm Qvkl Qvkm Qvlm Qvhkl Qvhkm Qvhlm Qvklm h k l m t)
          - (((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))) (R t)
             + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [heq]
  exact hcomb

set_option maxHeartbeats 6400000 in
/-- **The Jet_5 parameter-residual estimate, reduced to the remainder bound** (mirror of
    `expJet4_residual_bound`, one Frechet-derivative order higher).  With the Jet_4/Jet_5 data of
    `expJet5_residual_hasDerivWithinAt` and initial conditions `Qv 0 = Qw 0 = R 0 = 0`, given a
    `[0,1]`-bound `Kstar` on `||DF(Y_v t)||` and a `[0,1]`-bound `rho` on the remainder, one has
    `||Qw 1 - Qv 1 - R 1|| <= rho * e^{Kstar}`.

    Feeds the residual ODE (`expJet5_residual_hasDerivWithinAt`) into the vector Groenwall
    (`gronwall_vec_residual`).  Reduced to `||rho(t)|| <= rho` (carried honestly as `hr`); the
    quadratic bound `rho = C*||m||^2` is brick (b) -- NOT proven here. -/
theorem expJet5_residual_bound
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v w : Point n)
    (Φ Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qv Qw : ℝ → (Point n × Point n))
    (Qvhk Qvhl Qvhm Qvkl Qvkm Qvlm Qvhkl Qvhkm Qvhlm Qvklm : ℝ → (Point n × Point n))
    (Qwhk Qwhl Qwhm Qwkl Qwkm Qwlm Qwhkl Qwhkm Qwhlm Qwklm : ℝ → (Point n × Point n))
    (Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr : ℝ → (Point n × Point n))
    (Qhklm Qhklr Qhkmr Qhlmr Qklmr R : ℝ → (Point n × Point n)) (h k l m r : Point n)
    (hQv0 : Qv 0 = 0) (hQw0 : Qw 0 = 0) (hR0 : R 0 = 0)
    (hQvd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Qv
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qv t)
           + expJet4Rhs g gi hC p v Φ Qvhk Qvhl Qvhm Qvkl Qvkm Qvlm Qvhkl Qvhkm Qvhlm Qvklm h k l m t) (Set.Icc (0 : ℝ) 1) t)
    (hQwd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Qw
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qw t)
           + expJet4Rhs g gi hC p w Φ' Qwhk Qwhl Qwhm Qwkl Qwkm Qwlm Qwhkl Qwhkm Qwhlm Qwklm h k l m t) (Set.Icc (0 : ℝ) 1) t)
    (hRd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt R
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R t)
           + expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t) (Set.Icc (0 : ℝ) 1) t)
    (Kstar ρ : ℝ) (hKstar0 : 0 ≤ Kstar) (hρ0 : 0 ≤ ρ)
    (hKstar : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))‖ ≤ Kstar)
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t))
           - (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))) (Qw t)
         + (expJet4Rhs g gi hC p w Φ' Qwhk Qwhl Qwhm Qwkl Qwkm Qwlm Qwhkl Qwhkm Qwhlm Qwklm h k l m t
            - expJet4Rhs g gi hC p v Φ Qvhk Qvhl Qvhm Qvkl Qvkm Qvlm Qvhkl Qvhkm Qvhlm Qvklm h k l m t
            - expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t)‖ ≤ ρ) :
    ‖Qw 1 - Qv 1 - R 1‖ ≤ ρ * Real.exp Kstar := by
  refine gronwall_vec_residual (fun s => Qw s - Qv s - R s)
    (fun t => ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t))
        - (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))) (Qw t)
      + (expJet4Rhs g gi hC p w Φ' Qwhk Qwhl Qwhm Qwkl Qwkm Qwlm Qwhkl Qwhkm Qwhlm Qwklm h k l m t
         - expJet4Rhs g gi hC p v Φ Qvhk Qvhl Qvhm Qvkl Qvkm Qvlm Qvhkl Qvhkm Qvhlm Qvklm h k l m t
         - expJet5Rhs g gi hC p v Φ Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr Qhklm Qhklr Qhkmr Qhlmr Qklmr h k l m r t))
    (fun t => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t))) Kstar ρ hKstar0 hρ0
    ?_ ?_ hKstar hr
  · simp only [hQv0, hQw0, hR0, sub_self]
  · intro t ht
    exact expJet5_residual_hasDerivWithinAt g gi hC p v w Φ Φ' Qv Qw
      Qvhk Qvhl Qvhm Qvkl Qvkm Qvlm Qvhkl Qvhkm Qvhlm Qvklm
      Qwhk Qwhl Qwhm Qwkl Qwkm Qwlm Qwhkl Qwhkm Qwhlm Qwklm
      Qhk Qhl Qhm Qhr Qkl Qkm Qkr Qlm Qlr Qmr
      Qhkl Qhkm Qhkr Qhlm Qhlr Qhmr Qklm Qklr Qkmr Qlmr
      Qhklm Qhklr Qhkmr Qhlmr Qklmr R h k l m r
      hQvd hQwd hRd t ht

/-! ### Non-vacuity gate at the genuinely curved witness `curvedRNCMetric (−1)` -/

open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedA1CenterAmp in
set_option maxHeartbeats 6400000 in
/-- **Non-vacuity gate: the Jet_5 residual bound fires at genuinely curved data.**  At
    `g^kappa = curvedRNCMetric (−1)` (`p = 0`), taking all fourth/fifth-variation curves and
    propagators to `0` and base points `v = w = 0`, every hypothesis of `expJet5_residual_bound`
    is satisfiable (the tube Jacobi bound `Kstar` from `expJet_fderiv_tube_bddAbove`, the vanishing
    remainder `rho = 0`), so the endpoint bound `‖0 − 0 − 0‖ ≤ 0 · e^{Kstar}` holds THROUGH the
    theorem.  Certifies the order-5 residual bricks are non-vacuously instantiable at curved data
    (NOT a curvature computation and NOT `a_1 = R/6`). -/
theorem expJet5_residual_bound_gate :
    ∃ Kstar : ℝ, 0 ≤ Kstar ∧
      ‖(0 : Point n × Point n) - 0 - 0‖ ≤ (0 : ℝ) * Real.exp Kstar := by
  obtain ⟨Kstar, hKstar0, hKstar⟩ := expJet_fderiv_tube_bddAbove (curvedRNCMetric (n := n) (-1)) (curvedRNCInv (n := n) (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0
    (by rw [norm_zero]; exact (expRho_pos _ _ _ _).le)
  refine ⟨Kstar, hKstar0, ?_⟩
  -- the two source inhomogeneities collapse to `0` at the all-zero instantiation.
  have h4z : ∀ t : ℝ, expJet4Rhs (curvedRNCMetric (n := n) (-1)) (curvedRNCInv (n := n) (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 t = 0 := by
    intro t
    simp only [expJet4Rhs_apply, Pi.zero_apply, map_zero, add_zero]
  have h5z : ∀ t : ℝ, expJet5Rhs (curvedRNCMetric (n := n) (-1)) (curvedRNCInv (n := n) (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 t = 0 := by
    intro t
    simp only [expJet5Rhs_apply, Pi.zero_apply, map_zero, add_zero]
  have key := expJet5_residual_bound (curvedRNCMetric (n := n) (-1)) (curvedRNCInv (n := n) (-1)) (curvedRNC_hChr (-1) (by norm_num)) 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
    rfl rfl rfl
    (fun t _ => by
      simpa only [Pi.zero_apply, map_zero, h4z, add_zero, zero_add]
        using hasDerivWithinAt_const t (Set.Icc (0 : ℝ) 1) (0 : Point n × Point n))
    (fun t _ => by
      simpa only [Pi.zero_apply, map_zero, h4z, add_zero, zero_add]
        using hasDerivWithinAt_const t (Set.Icc (0 : ℝ) 1) (0 : Point n × Point n))
    (fun t _ => by
      simpa only [Pi.zero_apply, map_zero, h5z, add_zero, zero_add]
        using hasDerivWithinAt_const t (Set.Icc (0 : ℝ) 1) (0 : Point n × Point n))
    Kstar 0 hKstar0 le_rfl hKstar
    (fun t _ => by
      simp only [sub_self, h4z, h5z, Pi.zero_apply, map_zero,
        add_zero, norm_zero, le_refl])
  exact key

end QIQTH.ExpMap
