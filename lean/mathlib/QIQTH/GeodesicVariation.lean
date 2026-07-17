/-
  GeodesicVariation — the geodesic variational (linearized / first-order Jacobi) equation.

  ODE_VARIATIONAL_PLAN.md, Phase L1.  The linear variation `V(t)` of the geodesic flow — the
  initial-condition derivative of the geodesic solution `γ` in a tangent direction — satisfies the
  LINEARIZED ODE

        V'(t) = DF(γ(t)) · V(t),        F = geodesicField,  DF = fderiv ℝ F,

  the coefficient `A(t) = DF(γ(t))` being the honest Fréchet derivative of the phase-space geodesic
  field (`hasFDerivAt_geodesicField_fderiv`).  This is the first-order Jacobi equation — the first
  brick toward the (second-order) Jacobi equation.

  WHAT LANDS HERE (both axiom-clean, no `sorry`):

  * `geodesicVariation_velocity_hasDerivAt` — UNCONDITIONAL.  The velocity field along the geodesic,
    `V = F ∘ γ = γ'`, is a genuine solution of the variational equation: `V' = DF(γ)·V`.  This is the
    *tangential* Jacobi field (the derivative of the flow in its own time direction), obtained by the
    chain rule `d/dt F(γ t) = DF(γ t)·γ'(t)` with `γ'(t) = F(γ t)`.  No smooth-dependence input.

  * `geodesicVariation_hasDerivAt` — the general variational equation for the IC-linearization
    `V = ∂_s (Y s ·)|_{s=0}` of a one-parameter family `Y` of geodesics, CONDITIONAL on the two facts
    that constitute smooth dependence on the initial condition:
      (hV)   the IC-derivative EXISTS at each time (`HasDerivAt (fun s => Y s t) (V t) 0`);
      (hswap) the time- and parameter-derivatives INTERCHANGE
              (`∂_t V = ∂_s (F ∘ Y·t)|_{s=0}` — a mixed-partial / Clairaut fact).
    The chain-rule half (`∂_s F(Y s t)|_0 = DF(Y 0 t)·V t`) is DISCHARGED here from
    `hasFDerivAt_geodesicField_fderiv`; the two carried hypotheses are exactly the Mathlib-absent
    ODE-smooth-dependence-on-IC primitive.

  HONEST CHECKPOINT (binding): the *unconditional* variational equation holds for the tangential
  (velocity) variation only.  The GENERAL variation's equation is delivered CONDITIONALLY: the
  missing primitive is the smooth dependence of the geodesic flow on its initial condition — the
  existence AND t-differentiability of the IC-derivative, i.e. the mixed-partial interchange
  `∂_t ∂_s Y = ∂_s ∂_t Y`.  Mathlib has neither; the repo has first-order IC-smoothness (exp C¹) but
  not the interchange.  This file does NOT build the Jacobi equation (K3, second order), NOT
  Raychaudhuri, NOT the heat-kernel coefficient `a₁=R/6`.  It carries the smooth-dependence facts as
  genuine, clearly-labelled hypotheses (`hV`, `hswap`) and discharges everything else.
-/
import Mathlib
import QIQTH.ExpMap

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

variable {n : ℕ}

/-- **The geodesic variational (linearized / first-order Jacobi) ODE at time `t`.**  A phase-space
    curve `V : ℝ → Point n × Point n` is a *variation field* along the geodesic `γ` at `t` iff it
    solves the linearized ODE `V'(t) = DF(γ(t))·V(t)`, `F = geodesicField`, `DF = fderiv ℝ F`.  The
    coefficient `DF(γ t)` is the honest Fréchet derivative of the geodesic field
    (`hasFDerivAt_geodesicField_fderiv`), so this predicate is never junk. -/
def IsGeodesicVariationAt (g gi : Point n → Fin n → Fin n → ℝ)
    (γ V : ℝ → Point n × Point n) (t : ℝ) : Prop :=
  HasDerivAt V (fderiv ℝ (geodesicField g gi) (γ t) (V t)) t

/-- **The tangential (velocity) Jacobi field solves the variational equation — UNCONDITIONALLY.**
    Along any geodesic `γ` (a solution of the geodesic ODE `γ' = F(γ)` at `t`), the velocity field
    `V = F ∘ γ = γ'` satisfies the linearized ODE `V'(t) = DF(γ(t))·V(t)`.

    Proof: the chain rule `HasFDerivAt.comp_hasDerivAt` composes the field's Fréchet derivative
    (`hasFDerivAt_geodesicField_fderiv`) with the geodesic ODE (`hγ`), giving
    `d/dt F(γ t) = DF(γ t)·γ'(t)`; and `γ'(t) = F(γ t) = (F ∘ γ)(t) = V t`.

    This is the honest, input-free instance of the first-order Jacobi equation: the derivative of the
    geodesic flow along its OWN time direction.  It does NOT require smooth dependence on the initial
    condition (that is the general case, `geodesicVariation_hasDerivAt`). -/
theorem geodesicVariation_velocity_hasDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {γ : ℝ → Point n × Point n} {t : ℝ}
    (hγ : HasDerivAt γ (geodesicField g gi (γ t)) t) :
    IsGeodesicVariationAt g gi γ (fun τ => geodesicField g gi (γ τ)) t := by
  unfold IsGeodesicVariationAt
  have hcomp : HasDerivAt (fun τ => geodesicField g gi (γ τ))
      (fderiv ℝ (geodesicField g gi) (γ t) (geodesicField g gi (γ t))) t := by
    have := HasFDerivAt.comp_hasDerivAt (f := γ) (x := t)
      (hasFDerivAt_geodesicField_fderiv g gi hC (γ t)) hγ
    simpa [Function.comp] using this
  simpa using hcomp

/-- **The general geodesic variational equation — CONDITIONAL on smooth dependence on the initial
    condition.**  Let `Y : ℝ → ℝ → Point n × Point n` be a one-parameter family of curves (first
    argument `s` = variation parameter, second = time `t`), and let `V` be its initial-condition
    linearization `V(t) = ∂_s Y(s,t)|_{s=0}`.  Then `V` solves the variational ODE
    `V'(t) = DF(Y(0,·)(t))·V(t)`.

    The two carried hypotheses are EXACTLY the ODE-smooth-dependence-on-initial-condition primitive
    that Mathlib lacks (and that the repo has only at first order):
      * `hV`   — the IC-derivative EXISTS at time `t`: `HasDerivAt (fun s => Y s t) (V t) 0`.
      * `hswap` — the time- and parameter-derivatives INTERCHANGE:
                  `∂_t V = ∂_s (F ∘ Y(·,t))|_{s=0}` (the Clairaut / mixed-partial fact).

    Everything else is DISCHARGED: the chain rule `∂_s F(Y s t)|_{s=0} = DF(Y 0 t)·V(t)` follows from
    the field's Fréchet derivative (`hasFDerivAt_geodesicField_fderiv`) and `hV`; rewriting the
    interchange `hswap` through this identity yields the clean `V' = DF·V` form.

    HONEST: this is the variational equation for a GENERAL variation, but it is conditional — the two
    hypotheses are the genuine missing analytic input (smooth dependence of the geodesic flow on its
    initial condition).  Neither hypothesis is the conclusion: `hswap` is phrased via the raw
    parameter-derivative `deriv (fun s => F (Y s t)) 0` of the field composition, which we then PROVE
    equals `DF(Y 0 t)·V(t)` by the chain rule. -/
theorem geodesicVariation_hasDerivAt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {Y : ℝ → ℝ → Point n × Point n} {V : ℝ → Point n × Point n} {t : ℝ}
    (hV : HasDerivAt (fun s => Y s t) (V t) 0)
    (hswap : HasDerivAt V (deriv (fun s => geodesicField g gi (Y s t)) 0) t) :
    IsGeodesicVariationAt g gi (Y 0) V t := by
  unfold IsGeodesicVariationAt
  -- chain rule: the parameter-derivative of the field composition equals `DF(Y 0 t)·(V t)`.
  have hchain : HasDerivAt (fun s => geodesicField g gi (Y s t))
      (fderiv ℝ (geodesicField g gi) (Y 0 t) (V t)) 0 := by
    have := HasFDerivAt.comp_hasDerivAt (f := fun s => Y s t) (x := (0 : ℝ))
      (hasFDerivAt_geodesicField_fderiv g gi hC (Y 0 t)) hV
    simpa [Function.comp] using this
  -- rewrite the interchange hypothesis through the chain-rule identity.
  rwa [hchain.deriv] at hswap

end QIQTH.ExpMap
