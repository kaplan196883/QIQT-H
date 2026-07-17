/-
  JacobiEquation — the SECOND-ORDER geodesic-deviation (Jacobi) equation.

  ODE_VARIATIONAL_PLAN.md, Phase L2.  L1+L2a+L2b established the FIRST-order variational equation
  `V' = DF(γ)·V` (`IsGeodesicVariationAt`, `geodesicVariation_exists_uncond`): the Jacobi field
  exists and solves the linearized ODE.  This brick differentiates it ONCE MORE to reach the
  second-order geodesic-deviation form.

  In phase space `γ = (x, v)`, the geodesic field is `F(x,v) = (v, −Γ_x(v,v))`
  (`geodesicField`), and its Fréchet derivative is (`geodesicField_fderiv_apply`)
      `DF(x,v)(ξ,η) = (η, i ↦ −∑_{jk}[(∑_l ∂_l Γ^i_{jk}(x)·ξ_l)·v_j·v_k
                                       + Γ^i_{jk}(x)·η_j·v_k + Γ^i_{jk}(x)·v_j·η_k])`.
  So a variational field `V = (ξ,η)` solving `V' = DF(γ)·V` obeys `ξ' = η` and
      `η'^i = −∑_{jk}[(∑_l ∂_l Γ^i_{jk}·ξ_l)·v_j·v_k + Γ^i_{jk}·η_j·v_k + Γ^i_{jk}·v_j·η_k]`.
  Eliminating `η = ξ'` gives the position part `ξ'' = −(jacobiOperator)`, whose coefficient is (up
  to the coordinate/covariant correction) the Riemann curvature — the Jacobi equation
  `D²ξ/dτ² + R(ξ,γ')γ' = 0`.

  WHAT LANDS HERE (all axiom-clean, no `sorry`):

  #1  `jacobiOperator` (def) — the exact acceleration coefficient `ξ,η ↦ ∑_{jk}[(∂Γ·ξ)v v + Γ η v +
       Γ v η]` read off from `geodesicField_fderiv_apply`, with `DF(x,v)(ξ,η) = (η, −jacobiOperator)`
       (`geodesicField_fderiv_eq_jacobiOperator`).

  #2  `jacobiVariation_secondOrder` — the SECOND-order form: for a Jacobi field `V=(ξ,η)`
      (`IsGeodesicVariationAt` on a neighbourhood), the position part satisfies
      `ξ'' = −jacobiOperator g gi x v ξ η` (`HasDerivAt (deriv (fun τ => (V τ).1)) (−jacobiOperator …) t`),
      by differentiating the first-order system `ξ'=η, η'=−jacobiOperator` once more via the C² field
      structure.  Pure differentiation; no curvature yet.  UNCONDITIONAL given the first-order system.

  #3 (CHECKPOINT — the curvature identification, the deepest analytic core).  The genuine Jacobi
      equation is `D²ξ/dτ² + R(ξ,γ')γ' = 0` with the COVARIANT second derivative `D²/dτ²`.  The naive
      COORDINATE identity `jacobiOperator = R(ξ,v)v` is FALSE — the two differ by exactly the
      coordinate/covariant correction (the Christoffel terms distinguishing `ξ''` from `D²ξ/dτ²`).
      LANDED here as precise, honest partials that isolate the curvature step:
        * `jacobiOperator_at_center` — at a Riemann-normal-coordinate CENTRE (`Γ(x)=0`) the connection
          terms drop, `jacobiOperator = ∑_{jk}(∑_l ∂_l Γ^i_{jk}·ξ_l)·v_j·v_k`, independent of `η`.
        * `riemann_at_center` — at the centre the `ΓΓ` part drops, `R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} − ∂_ν Γ^ρ_{μσ}`.
        * `riemannGeodesicDeviation` (def) `R^i_{σμν} v^σ ξ^μ v^ν` and
          `riemannDeviation_at_center` — the deviation at the centre equals the ANTISYMMETRIZED
          `∂Γ` contraction, exhibiting precisely how it relates to the (non-antisymmetric)
          `jacobiOperator`.
        * `jacobiVariation_secondOrder_centered` — putting #2 at the centre: `ξ'' = −∑_{jkl} ∂_l Γ^i_{jk}
          ξ_l v_j v_k`, the pure `∂Γ` Jacobi form (the coefficient one antisymmetrizes to reach `R`).

  HONEST CHECKPOINT (binding).  #1 (operator) and #2 (the second-order ODE `ξ''=−jacobiOperator`) are
  UNCONDITIONAL (given the first-order variational system, itself the Jacobi-field existence of L2b).
  #3 is CHECKPOINTED: the literal operator↦Riemann identity is FALSE in coordinates; the curvature
  `R` appears only in the COVARIANT second derivative `D²ξ/dτ²`, which requires the along-the-curve
  covariant-derivative machinery to absorb the coordinate correction.  What is landed at the centre
  isolates the exact discrepancy — `jacobiOperator` is one `∂Γ` term while `R` is its
  antisymmetrization plus `ΓΓ`.  This file does NOT build the covariant `D²/dτ²`, NOT Raychaudhuri
  (L3), NOT the heat-kernel coefficient `a₁ = R/6`.  All regularity (`hC`: Γ is `C^∞`) and gauge
  (`Γ(x)=0` at the centre) inputs are carried as genuine, clearly-labelled hypotheses.
-/
import Mathlib
import QIQTH.ExpMap
import QIQTH.GeodesicVariation
import QIQTH.GeodesicSmoothDep

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxHeartbeats 1000000

variable {n : ℕ}

/-! ### #1 — the Jacobi (geodesic-deviation) operator -/

/-- **The Jacobi (geodesic-deviation) operator** — the acceleration coefficient of the first-order
    variational system, read off from `geodesicField_fderiv_apply`.  With `γ=(x,v)` a geodesic and
    `V=(ξ,η)` a variation field solving `V'=DF(γ)·V`, the acceleration part of `DF(x,v)(ξ,η)` is
    `−jacobiOperator g gi x v ξ η`, where
    `jacobiOperator^i = ∑_{jk}[(∑_l ∂_l Γ^i_{jk}(x)·ξ_l)·v_j·v_k + Γ^i_{jk}(x)·η_j·v_k
                              + Γ^i_{jk}(x)·v_j·η_k]`.
    The `∂Γ·ξ·v·v` term is the curvature-carrying piece; the two `Γ·η·v` terms are the
    coordinate connection terms (they vanish at a Riemann-normal-coordinate centre). -/
noncomputable def jacobiOperator (g gi : Point n → Fin n → Fin n → ℝ)
    (x v ξ η : Point n) : Point n :=
  fun i => ∑ j, ∑ k,
    ((∑ l, pd (fun z => christoffel g gi i j k z) l x * ξ l) * v j * v k
      + christoffel g gi i j k x * η j * v k
      + christoffel g gi i j k x * v j * η k)

/-- **The geodesic field's Fréchet derivative in Jacobi-operator form.**
    `DF(x,v)(ξ,η) = (η, −jacobiOperator g gi x v ξ η)` — a direct repackaging of
    `geodesicField_fderiv_apply` through the `jacobiOperator` definition. -/
theorem geodesicField_fderiv_eq_jacobiOperator (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (x v ξ η : Point n) :
    fderiv ℝ (geodesicField g gi) ((x, v) : Point n × Point n) ((ξ, η) : Point n × Point n)
      = ((η, -jacobiOperator g gi x v ξ η) : Point n × Point n) := by
  rw [geodesicField_fderiv_apply g gi hC x v ξ η]
  refine Prod.ext rfl ?_
  funext i
  simp only [jacobiOperator, Pi.neg_apply]

/-! ### #2 — the second-order Jacobi ODE `ξ'' = −jacobiOperator` -/

/-- **The second-order geodesic-deviation (Jacobi) ODE — UNCONDITIONAL given the first-order system.**
    Let `V=(ξ,η)` solve the first-order variational equation `V'=DF(γ)·V` (`IsGeodesicVariationAt`)
    on a full neighbourhood (here: for every time), along a curve `γ=(x,v)`.  Then the POSITION part
    `ξ = (V·).1` is twice differentiable with
        `ξ''(t) = −jacobiOperator g gi (γ t).1 (γ t).2 (ξ t) (η t)`,
    i.e. `HasDerivAt (deriv (fun τ => (V τ).1)) (−jacobiOperator …) t`.

    Proof: the first-order system gives `ξ' = η` (the first component of `DF(γ)V` is `η`) at every
    time, so `deriv ξ = η`; differentiating the second component `η' = (DF(γ)V).2 = −jacobiOperator`
    once more (it is delivered directly by the first-order equation) yields the second-order form.
    Purely the differentiation of the first-order system — no curvature identification. -/
theorem jacobiVariation_secondOrder (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {γ V : ℝ → Point n × Point n} {t : ℝ}
    (hVar : ∀ τ, IsGeodesicVariationAt g gi γ V τ) :
    HasDerivAt (deriv (fun τ => (V τ).1))
      (-jacobiOperator g gi (γ t).1 (γ t).2 (V t).1 (V t).2) t := by
  -- the `DF` value in Jacobi-operator form at each time.
  have hval : ∀ τ, fderiv ℝ (geodesicField g gi) (γ τ) (V τ)
      = ((V τ).2, -jacobiOperator g gi (γ τ).1 (γ τ).2 (V τ).1 (V τ).2) := by
    intro τ
    have := geodesicField_fderiv_eq_jacobiOperator g gi hC (γ τ).1 (γ τ).2 (V τ).1 (V τ).2
    simpa using this
  -- first component of the first-order system: `ξ' = η` at every time.
  have hfst : ∀ τ, HasDerivAt (fun τ' => (V τ').1) ((V τ).2) τ := by
    intro τ
    have h := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt τ (hVar τ)
    rw [hval τ] at h
    simpa using h
  -- hence `deriv ξ = η` as functions.
  have hderiv : deriv (fun τ' => (V τ').1) = fun τ => (V τ).2 :=
    funext (fun τ => (hfst τ).deriv)
  -- second component of the first-order system: `η' = −jacobiOperator` at `t`.
  have hsnd : HasDerivAt (fun τ' => (V τ').2)
      (-jacobiOperator g gi (γ t).1 (γ t).2 (V t).1 (V t).2) t := by
    have h := (ContinuousLinearMap.snd ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt t (hVar t)
    rw [hval t] at h
    simpa using h
  rw [hderiv]
  exact hsnd

/-! ### #3 — the curvature identification (CHECKPOINT)

  The genuine Jacobi equation is `D²ξ/dτ² + R(ξ,γ')γ' = 0` with the COVARIANT second derivative.  The
  literal coordinate identity `jacobiOperator = R(ξ,v)v` is FALSE; `R` surfaces only after passing to
  the covariant derivative.  We land the precise partials at a Riemann-normal-coordinate CENTRE that
  isolate exactly where the curvature enters. -/

/-- **`jacobiOperator` at a Riemann-normal-coordinate centre.**  Where the Christoffel symbols vanish
    (`Γ(x)=0` — the RNC gauge at the base point), the two `Γ·η·v` connection terms drop and the Jacobi
    operator reduces to the pure `∂Γ` term, independent of the velocity variation `η`:
    `jacobiOperator^i = ∑_{jk}(∑_l ∂_l Γ^i_{jk}(x)·ξ_l)·v_j·v_k`. -/
theorem jacobiOperator_at_center (g gi : Point n → Fin n → Fin n → ℝ)
    {x : Point n} (hΓ0 : ∀ i j k, christoffel g gi i j k x = 0) (v ξ η : Point n) :
    jacobiOperator g gi x v ξ η
      = fun i => ∑ j, ∑ k, (∑ l, pd (fun z => christoffel g gi i j k z) l x * ξ l) * v j * v k := by
  funext i
  simp only [jacobiOperator]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [hΓ0 i j k]; ring

/-- **The Riemann tensor at a Riemann-normal-coordinate centre.**  Where `Γ(x)=0`, the quadratic `ΓΓ`
    part of the curvature drops and only the derivative part remains:
    `R^ρ_{σμν}(x) = ∂_μ Γ^ρ_{νσ}(x) − ∂_ν Γ^ρ_{μσ}(x)`. -/
theorem riemann_at_center (g gi : Point n → Fin n → Fin n → ℝ)
    {x : Point n} (hΓ0 : ∀ i j k, christoffel g gi i j k x = 0) (ρ σ μ ν : Fin n) :
    riemann g gi ρ σ μ ν x
      = pd (fun y => christoffel g gi ρ ν σ y) μ x - pd (fun y => christoffel g gi ρ μ σ y) ν x := by
  simp only [riemann]
  rw [Finset.sum_eq_zero (fun l _ => by rw [hΓ0 ρ μ l, hΓ0 ρ ν l]; ring), add_zero]

/-- **The Riemann geodesic-deviation contraction** `R(ξ,v)v` (index form
    `R^i_{σμν} v^σ ξ^μ v^ν`) — the curvature coefficient of the covariant Jacobi equation
    `D²ξ/dτ² + R(ξ,γ')γ' = 0`. -/
noncomputable def riemannGeodesicDeviation (g gi : Point n → Fin n → Fin n → ℝ)
    (x v ξ : Point n) : Point n :=
  fun i => ∑ σ, ∑ μ, ∑ ν, riemann g gi i σ μ ν x * v σ * ξ μ * v ν

/-- **The geodesic-deviation contraction at a Riemann-normal-coordinate centre.**  Where `Γ(x)=0`,
    the curvature contraction reduces to the ANTISYMMETRIZED `∂Γ` contraction
    `R(ξ,v)v^i = ∑_{σμν}(∂_μ Γ^i_{νσ} − ∂_ν Γ^i_{μσ})·v^σ ξ^μ v^ν`.  Contrast with
    `jacobiOperator_at_center` (`∑_{jk}(∑_l ∂_l Γ^i_{jk}·ξ_l)·v_j·v_k`, a SINGLE non-antisymmetrized
    `∂Γ` term): the curvature is the antisymmetrization, and the difference is exactly the
    coordinate/covariant correction distinguishing `ξ''` from `D²ξ/dτ²`. -/
theorem riemannDeviation_at_center (g gi : Point n → Fin n → Fin n → ℝ)
    {x : Point n} (hΓ0 : ∀ i j k, christoffel g gi i j k x = 0) (v ξ : Point n) :
    riemannGeodesicDeviation g gi x v ξ
      = fun i => ∑ σ, ∑ μ, ∑ ν,
          (pd (fun y => christoffel g gi i ν σ y) μ x
            - pd (fun y => christoffel g gi i μ σ y) ν x) * v σ * ξ μ * v ν := by
  funext i
  simp only [riemannGeodesicDeviation]
  refine Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun μ _ =>
    Finset.sum_congr rfl (fun ν _ => ?_)))
  rw [riemann_at_center g gi hΓ0 i σ μ ν]

/-- **#2 at a Riemann-normal-coordinate centre — the pure `∂Γ` Jacobi form.**  Combining
    `jacobiVariation_secondOrder` with `jacobiOperator_at_center`: at a base time `t` where the
    Christoffel symbols vanish at the base point `Γ((γ t).1)=0`, the position variation obeys
    `ξ''(t) = −∑_{jk}(∑_l ∂_l Γ^i_{jk}·ξ_l)·v_j·v_k`.  This is the coefficient one antisymmetrizes to
    reach the Riemann curvature `R(ξ,v)v` (see `riemannDeviation_at_center`) — the remaining step is
    the covariant-derivative correction, the checkpointed crux. -/
theorem jacobiVariation_secondOrder_centered (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {γ V : ℝ → Point n × Point n} {t : ℝ}
    (hVar : ∀ τ, IsGeodesicVariationAt g gi γ V τ)
    (hΓ0 : ∀ i j k, christoffel g gi i j k (γ t).1 = 0) :
    HasDerivAt (deriv (fun τ => (V τ).1))
      (-(fun i => ∑ j, ∑ k,
          (∑ l, pd (fun z => christoffel g gi i j k z) l (γ t).1 * (V t).1 l) * (γ t).2 j * (γ t).2 k))
      t := by
  have h := jacobiVariation_secondOrder g gi hC hVar (γ := γ) (V := V) (t := t)
  rwa [jacobiOperator_at_center g gi hΓ0 (γ t).2 (V t).1 (V t).2] at h

end QIQTH.ExpMap
