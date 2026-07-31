/-
  BasepointJacobi2 — J4-27 (d1 foundation): the BASE-POINT second-order Jacobi / second-order
  variation equation, mirroring the velocity-side `jacobiVariation_secondOrder`.

  ODE_VARIATIONAL_PLAN.md, Phase J-d preparation.  The base-point smooth-dependence campaign is
  reduced (J4-26, `BasepointSecondJet`) to the single input `hunif` — the base-point uniform modulus
  of the velocity 2-jet.  The plan to close `hunif` runs through the base-point SECOND-order jet
  (`HasFDerivAt (fun δ => V δ t) L₂ 0`), and that jet builds on the base-point SECOND-order Jacobi
  ODE `ξ'' = −jacobiOperator` for the base-point-seeded Jacobi field — the object this file lands.

  KEY OBSERVATION (verified by re-reading `JacobiEquation.jacobiVariation_secondOrder`).  That lemma is
  stated for a velocity Jacobi field in its NARRATIVE, but its STATEMENT and PROOF take an ARBITRARY
  curve `γ` and an ARBITRARY variation field `V` obeying `IsGeodesicVariationAt g gi γ V τ` — the
  initial-condition direction (`(0,w)` velocity vs `(δ,0)` base-point) is NEVER used.  This is exactly
  the J4-23 phenomenon (`geodesicVariation_exists` was velocity-only in statement, not in proof): the
  second-order Jacobi ODE is already direction-agnostic, so the base-point ("one direction slot over")
  case is a verbatim instantiation `V := V δ`, NOT a re-proof.

  WHAT LANDS HERE (all axiom-clean, no `sorry`; DERIVED; carrying only the SAME genuine variation-ODE
  input the velocity side carries — the Jacobi/variation equation `IsGeodesicVariationAt`, phrased on a
  neighbourhood or globally, NOT the conclusion):

  * `jacobiVariation_secondOrder_local` — the genuinely-new **LOCAL** form: the second-order Jacobi ODE
    `ξ'' = −jacobiOperator` holds at `t` needing the first-order variation equation only on a
    NEIGHBOURHOOD of `t` (`∀ᶠ τ in 𝓝 t, IsGeodesicVariationAt …`) instead of for every time.  Re-proved
    via the `EventuallyEq`-congruence of `deriv ξ` with the velocity part `η` on that neighbourhood.
    This is what lets a family whose variation ODE is only known on `[0,1]` (the base-point setup) feed
    the second-order ODE at INTERIOR times with no global assumption.

  * `jacobiVariation_secondOrder_dir` — the base-point ("one direction slot over") packaging: for a
    base-point-perturbation-indexed family `V : Point n → ℝ → State` with direction `δ`, the
    base-point-seeded Jacobi field `V δ` satisfies `ξ'' = −jacobiOperator`.  A verbatim instantiation of
    `jacobiVariation_secondOrder` at `V := V δ`, `γ := W 0` — the direction-agnostic KEY OBSERVATION made
    concrete.  Carries the SAME global variation-ODE input the velocity side carries.

  * `jacobiVariation_secondOrder_basepoint` — the family bridge: consuming exactly the
    `BasepointFDeriv`-style hypothesis shape (`hVode`: the variation ODE for `V δ` on `Set.Icc 0 1`),
    it delivers the base-point second-order Jacobi ODE at any INTERIOR time `t ∈ Set.Ioo 0 1` (where
    `Icc 0 1 ∈ 𝓝 t`), via `jacobiVariation_secondOrder_local`.  NO global assumption; the `[0,1]` ODE
    suffices for interior `t`.

  HONEST CHECKPOINT (binding).  This lands the base-point SECOND-order Jacobi ODE `ξ'' = −jacobiOperator`
  for the base-point-seeded field, DERIVED from the (carried) first-order variation equation.  It does
  NOT build the base-point second-order JET `HasFDerivAt (fun δ => V δ t) L₂ 0` (J-d, needs a supplied
  second-order variation field + the cubic remainder `decay_order_three_remainder_convex`), NOT the
  uniform bound over `K × B̄`, NOT `hunif`, NOT Raychaudhuri (L3), NOT `a₁ = R/6`.
-/
import QIQTH.JacobiEquation
import QIQTH.BasepointSmoothDep
import QIQTH.BasepointFDeriv
import QIQTH.DecayOrderThree
import Mathlib

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxHeartbeats 1000000

variable {n : ℕ}

/-- **The second-order Jacobi ODE — LOCAL form.**  Let `V = (ξ,η)` obey the first-order variation
    equation `V' = DF(γ)·V` (`IsGeodesicVariationAt`) on a NEIGHBOURHOOD of `t` only (rather than for
    every time, as in `jacobiVariation_secondOrder`).  Then the position part `ξ = (V·).1` satisfies the
    second-order geodesic-deviation (Jacobi) ODE at `t`:
        `ξ''(t) = −jacobiOperator g gi (γ t).1 (γ t).2 (ξ t) (η t)`.

    Proof: the neighbourhood hypothesis gives `deriv ξ = η` on that neighbourhood (each point's first
    component of the first-order system is `ξ' = η`), so `deriv ξ =ᶠ[𝓝 t] η`; differentiating the second
    component `η' = −jacobiOperator` once at `t` (delivered by the first-order equation there) and
    transporting along the `EventuallyEq` yields the second-order form.  Pure differentiation localised
    to a neighbourhood — no curvature identification, no global assumption. -/
theorem jacobiVariation_secondOrder_local (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {γ V : ℝ → Point n × Point n} {t : ℝ}
    (hVar : ∀ᶠ τ in nhds t, IsGeodesicVariationAt g gi γ V τ) :
    HasDerivAt (deriv (fun τ => (V τ).1))
      (-jacobiOperator g gi (γ t).1 (γ t).2 (V t).1 (V t).2) t := by
  -- the `DF` value in Jacobi-operator form at each time.
  have hval : ∀ τ, fderiv ℝ (geodesicField g gi) (γ τ) (V τ)
      = ((V τ).2, -jacobiOperator g gi (γ τ).1 (γ τ).2 (V τ).1 (V τ).2) := by
    intro τ
    have := geodesicField_fderiv_eq_jacobiOperator g gi hC (γ τ).1 (γ τ).2 (V τ).1 (V τ).2
    simpa using this
  -- first component of the first-order system: `ξ' = η`, hence `deriv ξ = η`, on the neighbourhood.
  have hderiv_ev : (deriv (fun τ' => (V τ').1)) =ᶠ[nhds t] (fun τ => (V τ).2) := by
    filter_upwards [hVar] with τ hτ
    have h := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt τ hτ
    rw [hval τ] at h
    exact (show HasDerivAt (fun τ' => (V τ').1) ((V τ).2) τ by simpa using h).deriv
  -- second component of the first-order system at `t`: `η' = −jacobiOperator`.
  have hVart : IsGeodesicVariationAt g gi γ V t := hVar.self_of_nhds
  have hsnd : HasDerivAt (fun τ' => (V τ').2)
      (-jacobiOperator g gi (γ t).1 (γ t).2 (V t).1 (V t).2) t := by
    have h := (ContinuousLinearMap.snd ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt t hVart
    rw [hval t] at h
    simpa using h
  exact hsnd.congr_of_eventuallyEq hderiv_ev

/-- **The base-point second-order Jacobi ODE — "one direction slot over".**  For a base-point-
    perturbation-indexed family of variation fields `V : Point n → ℝ → State` and a fixed base-point
    direction `δ`, the base-point-seeded Jacobi field `V δ` (along the base geodesic `W 0`) satisfies the
    same second-order geodesic-deviation ODE as the velocity field:
        `ξ_δ''(t) = −jacobiOperator g gi (W 0 t).1 (W 0 t).2 (V δ t).1 (V δ t).2`.

    This is a VERBATIM instantiation of `jacobiVariation_secondOrder` at `γ := W 0`, `V := V δ`: that
    lemma never uses the initial-condition direction, so the base-point (position-slot `(δ,0)`) seed
    obeys the second-order ODE for free — the direction-agnostic key observation made concrete.  Carries
    the SAME genuine variation-ODE input the velocity side carries (the first-order Jacobi equation for
    all times). -/
theorem jacobiVariation_secondOrder_dir (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W V : Point n → ℝ → Point n × Point n} {δ : Point n} {t : ℝ}
    (hVar : ∀ τ, IsGeodesicVariationAt g gi (W 0) (V δ) τ) :
    HasDerivAt (deriv (fun τ => (V δ τ).1))
      (-jacobiOperator g gi (W 0 t).1 (W 0 t).2 (V δ t).1 (V δ t).2) t :=
  jacobiVariation_secondOrder g gi hC hVar

/-- **The base-point second-order Jacobi ODE from the `BasepointFDeriv` family data.**  Consuming
    exactly the base-point-family hypothesis shape carried by `BasepointFDeriv`/`BasepointSmoothDep`
    (`hVode`: the first-order variation ODE for `V δ` along the base geodesic `W 0` on `Set.Icc 0 1`),
    the base-point-seeded Jacobi field `V δ` satisfies the second-order Jacobi ODE at any INTERIOR time
    `t ∈ Set.Ioo 0 1`:
        `ξ_δ''(t) = −jacobiOperator g gi (W 0 t).1 (W 0 t).2 (V δ t).1 (V δ t).2`.

    DERIVED via `jacobiVariation_secondOrder_local`: `Set.Icc 0 1 ∈ 𝓝 t` for interior `t`, so the
    variation ODE known only on `[0,1]` is a neighbourhood hypothesis at `t` — NO global assumption
    needed.  This is the exact bridge that lets the base-point family (whose ODE is confined to `[0,1]`)
    feed the second-order jet at interior times. -/
theorem jacobiVariation_secondOrder_basepoint (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {W V : Point n → ℝ → Point n × Point n} {δ : Point n} {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hVode : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (V δ) (fderiv ℝ (geodesicField g gi) (W 0 τ) (V δ τ)) τ) :
    HasDerivAt (deriv (fun τ => (V δ τ).1))
      (-jacobiOperator g gi (W 0 t).1 (W 0 t).2 (V δ t).1 (V δ t).2) t := by
  apply jacobiVariation_secondOrder_local g gi hC
  have hmem : Set.Icc (0 : ℝ) 1 ∈ nhds t := Icc_mem_nhds ht.1 ht.2
  filter_upwards [hmem] with τ hτ
  exact hVode τ hτ

end QIQTH.ExpMap
