/-
Copyright (c) 2026 Pawel Kaplanski. All rights reserved.
Released under Apache 2.0 license.
-/
import QIQTH.ExpJet4Rhs

/-!
# Jet₄ parameter-residual ODE and its Grönwall endpoint bound — rung J4-5a

This file lands the **J4-5a brick** of the JET-4 TOWER campaign toward the truly-unconditional
`a₁ = R/6`: the first sub-brick of the order-4 quadratic-remainder chain toward
`expMap_fderiv3_hasFDerivAt`.  It is a FAITHFUL MIRROR, one Fréchet-derivative order higher, of the
landed Jet₃ residual bricks `expJet3_residual_hasDerivWithinAt` / `expJet3_residual_bound`
(`ExpMapContDiff3.lean`).

Concretely, with `Qv`,`Qw` the order-3 (third-variation) fundamental solutions (source
`expJet3Rhs`) for base points `v` and `w = v + m`, and `R` the order-4 (fourth-variation) solution
(source `expJet4Rhs`) for base `v`, the **residual** `S(t) = Qw(t) − Qv(t) − R(t)` solves, on
`[0,1]`, the inhomogeneous linear ODE

  `S'(t) = DF(Y_v t)(S t) + ρ(t)`,
  `ρ(t) = [DF(Y_w t) − DF(Y_v t)](Qw t) + (Θ₃^{hkl}_w(t) − Θ₃^{hkl}_v(t) − Θ₄^{hklm}_v(t))`,

with `S(0) = 0`.  Feeding this into the vector Grönwall `gronwall_vec_residual` gives the endpoint
bound `‖Qw 1 − Qv 1 − R 1‖ ≤ ρ · e^{Kstar}`.

## Honest firewall (binding)

`expJet4_residual_bound` reduces the residual estimate to the single `[0,1]`-uniform obligation
`‖ρ(t)‖ ≤ ρ` (carried as the honest explicit hypothesis `hr`, exactly as in the Jet₃ mirror), plus
the tube Jacobi bound `Kstar`.  The quadratic sharpening `ρ = C·‖m‖²` (which closes the Fréchet
little-o for `v ↦ Q^{hkl}_v(1)`, discharging `ContDiff¹ (fderiv³ exp_p)`) is the NEXT brick
(`expJet4_remainder_quadratic_bound`, mirror of `ExpMapContDiff3.lean:1605`) — NOT proven here.
-/

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

variable {n : ℕ}

/-- **The Jet₄ parameter-residual ODE identity** (mirror of `expJet3_residual_hasDerivWithinAt`,
    one Fréchet-derivative order higher).  With `Qv`,`Qw` the order-3 (third-variation) fundamental
    solutions with source `expJet3Rhs` for base points `v` (curves `Qvkl,Qvhl,Qvhk`) and
    `w` (curves `Qwkl,Qwhl,Qwhk`), and `R` the order-4 (fourth-variation) solution with source
    `expJet4Rhs` for base `v`, the residual `S(t) = Qw(t) − Qv(t) − R(t)` obeys, on `[0,1]`,
    `S'(t) = DF(Y_v t)(S t) + ([DF(Y_w t) − DF(Y_v t)](Qw t) + (Θ₃^{hkl}_w(t) − Θ₃^{hkl}_v(t) − Θ₄^{hklm}_v(t)))`.

    Proof (mirror of the Jet₃ version): `Qw`,`Qv`,`R` solve their ODEs (`hQwd`,`hQvd`,`hRd`);
    `HasDerivWithinAt.sub` twice gives the natural difference derivative; `map_sub` (linearity of
    `DF(Y_v t)`) + `ContinuousLinearMap.sub_apply` + `abel` regroup it into the `DF(Y_v t)(S) + ρ`
    form. -/
theorem expJet4_residual_hasDerivWithinAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v w : Point n)
    (Φ Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qv Qw : ℝ → (Point n × Point n))
    (Qvkl Qvhl Qvhk Qwkl Qwhl Qwhk : ℝ → (Point n × Point n))
    (Qhk Qhl Qhm Qkl Qkm Qlm : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhlm Qklm R : ℝ → (Point n × Point n)) (h k l m : Point n)
    (hQvd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Qv
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qv t)
           + expJet3Rhs g gi hC p v Φ Qvkl Qvhl Qvhk h k l t) (Set.Icc (0 : ℝ) 1) t)
    (hQwd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Qw
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qw t)
           + expJet3Rhs g gi hC p w Φ' Qwkl Qwhl Qwhk h k l t) (Set.Icc (0 : ℝ) 1) t)
    (hRd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt R
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R t)
           + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)
        (Set.Icc (0 : ℝ) 1) t)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun s => Qw s - Qv s - R s)
      ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qw t - Qv t - R t)
        + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)
             - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qw t)
           + (expJet3Rhs g gi hC p w Φ' Qwkl Qwhl Qwhk h k l t
              - expJet3Rhs g gi hC p v Φ Qvkl Qvhl Qvhk h k l t
              - expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)))
      (Set.Icc (0 : ℝ) 1) t := by
  -- the natural difference derivative from the three ODEs.
  have hcomb := ((hQwd t ht).sub (hQvd t ht)).sub (hRd t ht)
  -- rearrange the target derivative into the natural one via linearity.
  have heq :
      (fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qw t - Qv t - R t)
        + ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)
             - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qw t)
           + (expJet3Rhs g gi hC p w Φ' Qwkl Qwhl Qwhk h k l t
              - expJet3Rhs g gi hC p v Φ Qvkl Qvhl Qvhk h k l t
              - expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t))
      = ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qw t)
            + expJet3Rhs g gi hC p w Φ' Qwkl Qwhl Qwhk h k l t)
          - ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qv t)
             + expJet3Rhs g gi hC p v Φ Qvkl Qvhl Qvhk h k l t)
          - ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R t)
             + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [heq]
  exact hcomb

set_option maxHeartbeats 1000000 in
/-- **The Jet₄ parameter-residual estimate, reduced to the remainder bound** (mirror of
    `expJet3_residual_bound`, one Fréchet-derivative order higher).  With the Jet₃/Jet₄
    third/fourth-variation data of `expJet4_residual_hasDerivWithinAt` and the initial conditions
    `Qv 0 = Qw 0 = R 0 = 0`, given a `[0,1]`-bound `Kstar` on `‖DF(Y_v t)‖` and a `[0,1]`-bound `ρ`
    on the remainder `‖[DF(Y_w t) − DF(Y_v t)](Qw t) + (Θ₃^{hkl}_w(t) − Θ₃^{hkl}_v(t) − Θ₄^{hklm}_v(t))‖`,
    one has `‖Qw 1 − Qv 1 − R 1‖ ≤ ρ · e^{Kstar}`.

    Feeds the residual ODE (`expJet4_residual_hasDerivWithinAt`) into the vector Grönwall
    (`gronwall_vec_residual`).  This is the residual estimate reduced to the single obligation
    `‖ρ(t)‖ ≤ ρ` (carried honestly as `hr`); the quadratic bound `ρ = C·‖m‖²` is the NEXT brick
    (`expJet4_remainder_quadratic_bound`) — NOT proven here. -/
theorem expJet4_residual_bound (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (p v w : Point n)
    (Φ Φ' : ℝ → ((Point n × Point n) →L[ℝ] (Point n × Point n)))
    (Qv Qw : ℝ → (Point n × Point n))
    (Qvkl Qvhl Qvhk Qwkl Qwhl Qwhk : ℝ → (Point n × Point n))
    (Qhk Qhl Qhm Qkl Qkm Qlm : ℝ → (Point n × Point n))
    (Qhkl Qhkm Qhlm Qklm R : ℝ → (Point n × Point n)) (h k l m : Point n)
    (hQv0 : Qv 0 = 0) (hQw0 : Qw 0 = 0) (hR0 : R 0 = 0)
    (hQvd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Qv
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qv t)
           + expJet3Rhs g gi hC p v Φ Qvkl Qvhl Qvhk h k l t) (Set.Icc (0 : ℝ) 1) t)
    (hQwd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt Qw
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)) (Qw t)
           + expJet3Rhs g gi hC p w Φ' Qwkl Qwhl Qwhk h k l t) (Set.Icc (0 : ℝ) 1) t)
    (hRd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt R
        ((fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (R t)
           + expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)
        (Set.Icc (0 : ℝ) 1) t)
    (Kstar ρ : ℝ) (hKstar0 : 0 ≤ Kstar) (hρ0 : 0 ≤ ρ)
    (hKstar : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)‖ ≤ Kstar)
    (hr : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)
           - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qw t)
         + (expJet3Rhs g gi hC p w Φ' Qwkl Qwhl Qwhk h k l t
            - expJet3Rhs g gi hC p v Φ Qvkl Qvhl Qvhk h k l t
            - expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t)‖ ≤ ρ) :
    ‖Qw 1 - Qv 1 - R 1‖ ≤ ρ * Real.exp Kstar := by
  refine gronwall_vec_residual (fun s => Qw s - Qv s - R s)
    (fun t => (fderiv ℝ (geodesicField g gi) (expTube g gi hC p w t)
        - fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) (Qw t)
      + (expJet3Rhs g gi hC p w Φ' Qwkl Qwhl Qwhk h k l t
         - expJet3Rhs g gi hC p v Φ Qvkl Qvhl Qvhk h k l t
         - expJet4Rhs g gi hC p v Φ Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm h k l m t))
    (fun t => fderiv ℝ (geodesicField g gi) (expTube g gi hC p v t)) Kstar ρ hKstar0 hρ0
    ?_ ?_ hKstar hr
  · -- initial condition `S 0 = 0`.
    simp only [hQv0, hQw0, hR0, sub_self]
  · -- the residual ODE.
    intro t ht
    exact expJet4_residual_hasDerivWithinAt g gi hC p v w Φ Φ' Qv Qw
      Qvkl Qvhl Qvhk Qwkl Qwhl Qwhk Qhk Qhl Qhm Qkl Qkm Qlm Qhkl Qhkm Qhlm Qklm R h k l m
      hQvd hQwd hRd t ht

end QIQTH.ExpMap
