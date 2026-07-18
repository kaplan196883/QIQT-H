/-
  CovariantJacobi — the COVARIANT Jacobi (geodesic-deviation) equation.

  ODE_VARIATIONAL_PLAN.md, Phase L2c.  L2 (`JacobiEquation`) proved the COORDINATE second-order ODE
  `ξ'' = −jacobiOperator` UNCONDITIONALLY, and found that the literal `jacobiOperator = R(ξ,v)v` is
  FALSE in coordinates: the genuine Jacobi equation is `D²ξ/dτ² = −R(ξ,γ')γ'` with the COVARIANT
  second derivative `D²/dτ²`.  This brick builds the along-the-curve covariant derivative and proves
  the covariant Jacobi equation from L2's coordinate ODE plus the covariant correction.

  WHAT LANDS HERE (all axiom-clean, no `sorry`):

  #1  `covariantDerivAlong` — the covariant derivative of a vector field `ξ(τ)` along a curve `γ(τ)`,
      `(Dξ/dτ)^i = (ξ^i)'(τ) + ∑_{jk} Γ^i_{jk}(γ τ)·(γ^j)'(τ)·ξ^k(τ)`, matching `christoffel`'s index
      convention.

  #2  `covariantSecondDeriv` — `D²ξ/dτ² := covariantDerivAlong g gi γ (covariantDerivAlong g gi γ ξ)`,
      with its definitional expansion `covariantSecondDeriv_apply`; plus `hasDerivAt_comp_curve` (the
      ray chain-rule helper).

  #3 (CENTERED) — the covariant Jacobi equation AT AN RNC CENTER (`hΓ0 : Γ(γ t) = 0`):
      `covariant_jacobi_equation_centered` : `D²ξ/dτ² = −R(ξ,v)v` (`= −riemannGeodesicDeviation`).
      KEY INSIGHT (`covariantSecondDeriv_at_center`): even where `Γ = 0`, the covariant second
      derivative is NOT just the coordinate `ξ''` — differentiating the connection term `Γ(v,ξ)` brings
      down a surviving `∂Γ` correction, `D²ξ/dτ²|^i = −(jacobiOperator)^i + ∑_{jk}(∑_a ∂_aΓ^i_{jk}·v^a)v^jξ^k`.
      Combined with L2's `ξ'' = −jacobiOperator` and the `∂Γ`-antisymmetrization (`covariantJacobi_finset_match`,
      via `Γ`-lower-symmetry + `v`-symmetry) this closes to exactly `−R(ξ,v)v`.

  ⚠ SCOPE — this is the CENTERED case only.  NOT built here: the OFF-CENTER covariant Jacobi identity
  (general `Γ ≠ 0`; the checkpoint two prior agents stalled on), Raychaudhuri / `r∂_r log J` (L3), and
  the heat-kernel coefficient `a₁ = R/6` (K6).  The diagonal `a₁` needs only the centered/diagonal
  structure, so the centered case is on the critical path; the off-center case stays a labelled checkpoint.

  All regularity/gauge inputs (`hgsymm`: metric symmetric; `hC`: Γ is `C^∞`; geodesic ODE `hγ`;
  variational ODE `hVar`; RNC-center gauge `hΓ0`) are carried as genuine, clearly-labelled hypotheses —
  none assume the conclusion.
-/
import Mathlib
import QIQTH.ExpMap
import QIQTH.Curvature
import QIQTH.JacobiEquation

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset Topology

set_option maxHeartbeats 4000000

variable {n : ℕ}

/-! ### #1 — the covariant derivative along a curve -/

/-- **The covariant derivative of a vector field `ξ` along a curve `γ`.**
    `(Dξ/dτ)^i = (ξ^i)'(τ) + ∑_{jk} Γ^i_{jk}(γ τ)·(γ^j)'(τ)·ξ^k(τ)`, with the Christoffel index
    convention `christoffel g gi i j k = Γ^i_{jk}`.  The ordinary coordinate derivative of `ξ^i`
    corrected by the connection term contracting the velocity `γ'` and the field `ξ`. -/
noncomputable def covariantDerivAlong (g gi : Point n → Fin n → Fin n → ℝ)
    (γ ξ : ℝ → Point n) (τ : ℝ) : Point n :=
  fun i => deriv (fun s => ξ s i) τ
    + ∑ j, ∑ k, christoffel g gi i j k (γ τ) * deriv (fun s => γ s j) τ * ξ τ k

/-- Componentwise form of `covariantDerivAlong` (definitional). -/
theorem covariantDerivAlong_apply (g gi : Point n → Fin n → Fin n → ℝ)
    (γ ξ : ℝ → Point n) (τ : ℝ) (i : Fin n) :
    covariantDerivAlong g gi γ ξ τ i
      = deriv (fun s => ξ s i) τ
        + ∑ j, ∑ k, christoffel g gi i j k (γ τ) * deriv (fun s => γ s j) τ * ξ τ k := rfl

/-! ### #2 — the covariant second derivative -/

/-- **The covariant second derivative** `D²ξ/dτ²` — apply `covariantDerivAlong` twice (the inner
    covariant derivative is itself a vector field along `γ`). -/
noncomputable def covariantSecondDeriv (g gi : Point n → Fin n → Fin n → ℝ)
    (γ ξ : ℝ → Point n) (τ : ℝ) : Point n :=
  covariantDerivAlong g gi γ (covariantDerivAlong g gi γ ξ) τ

/-- **Expansion of the covariant second derivative** (definitional): the outer covariant derivative of
    the inner covariant-derivative field.  `(D²ξ)^i = (Dξ^i)'(τ) + ∑_{jk} Γ^i_{jk}(γ τ)·(γ^j)'(τ)·(Dξ)^k(τ)`. -/
theorem covariantSecondDeriv_apply (g gi : Point n → Fin n → Fin n → ℝ)
    (γ ξ : ℝ → Point n) (τ : ℝ) (i : Fin n) :
    covariantSecondDeriv g gi γ ξ τ i
      = deriv (fun s => covariantDerivAlong g gi γ ξ s i) τ
        + ∑ j, ∑ k, christoffel g gi i j k (γ τ) * deriv (fun s => γ s j) τ
            * covariantDerivAlong g gi γ ξ τ k := rfl

/-! ### Helpers for #3 (curve chain rule) -/

/-- **Chain rule along a curve** in Christoffel-partial form: for a smooth scalar field `f` and a curve
    `c` with `HasDerivAt c c' τ`, `d/ds f(c s) = ∑ l, ∂_l f(c τ)·c'_l` (via `fderiv_apply_eq_sum_pd`). -/
theorem hasDerivAt_comp_curve (f : Point n → ℝ) (c : ℝ → Point n) (c' : Point n) (τ : ℝ)
    (hf : ContDiff ℝ (⊤ : WithTop ℕ∞) f) (hc : HasDerivAt c c' τ) :
    HasDerivAt (fun s => f (c s)) (∑ l, pd f l (c τ) * c' l) τ := by
  have hFD : HasFDerivAt f (fderiv ℝ f (c τ)) (c τ) :=
    (hf.differentiable (by simp) (c τ)).hasFDerivAt
  have h := hFD.comp_hasDerivAt τ hc
  rwa [fderiv_apply_eq_sum_pd f (c τ) c' (hf.differentiable (by simp) (c τ))] at h

/-! ### #3 — the covariant Jacobi equation (centered)

  L2c #3 (CENTERED), `ODE_VARIATIONAL_PLAN.md`.  The genuine geodesic-deviation equation
  `D²ξ/dτ² = −R(ξ,γ')γ'`, proved AT a Riemann-normal-coordinate CENTRE (where `Γ(γ t)=0`).

  KEY INSIGHT (why the naive `D²ξ = ξ''` is wrong even at the centre): the first covariant derivative
  is `Dξ/dτ = ξ' + Γ(x)(v,ξ)`, and its τ-derivative (the covariant second derivative) still
  differentiates the INNER connection term `Γ(x τ)(v,ξ)`, bringing down `∂Γ` — nonzero even where
  `Γ=0`.  At the centre the OUTER `Γ·(Dξ/dτ)` term and the `Γ·v'` term vanish, but the `∂Γ·v·ξ`
  correction survives:
    `D²ξ/dτ²|^i = ξ''^i + ∑_{a,j,k} ∂_aΓ^i_{jk}(x)·v^a·v^j·ξ^k`     (`covariantSecondDeriv_at_center`).
  Substituting L2's centred `ξ'' = −jacobiOperator` and matching against the antisymmetrized `∂Γ`
  contraction of `R(ξ,v)v` (`riemannDeviation_at_center`) closes the identity, using ONLY Christoffel
  lower-symmetry (`christoffel_symm`) and `v`-symmetry — the finite `Finset` identity
  `covariantJacobi_finset_match`.

  All regularity/gauge/dynamical inputs are carried as genuine, clearly-labelled hypotheses:
  `hC` (Γ smooth), `hgsymm` (metric symmetry ⟹ Christoffel lower-symmetry), the geodesic ODE `hγ`,
  the Jacobi-field variational ODE `hVar`, and the RNC-centre gauge `hΓ0`.  This lands the CENTERED
  covariant Jacobi equation only; the off-centre Finset identity, Raychaudhuri (L3), and `a₁=R/6`
  remain OUT of scope. -/

/-- **The covariant second derivative at a Riemann-normal-coordinate centre — the `∂Γ` correction.**
    For a geodesic `γ=(x,v)` (`hγ`) and a Jacobi field `V=(ξ,η)` (`hVar`), at a base time `t` where the
    Christoffel symbols vanish at the base point (`Γ(γ t).1 = 0`), the covariant second derivative of
    the position variation `ξ = (V·).1` along `x = (γ·).1` is the coordinate `ξ''` PLUS the surviving
    `∂Γ` correction from differentiating the inner connection term:
      `D²ξ/dτ²|^i = −(jacobiOperator)^i + ∑_{jk}(∑_a ∂_a Γ^i_{jk}(x)·v^a)·v^j·ξ^k`,
    where `ξ'' = −jacobiOperator` is L2's centred second-order form.  The outer `Γ·(Dξ)` term drops
    (`Γ(γ t).1 = 0`), and in the inner `Γ(x s)(v,ξ)` term only the derivative of `Γ∘x` survives — the
    `Γ·v'` and `Γ·ξ'` pieces are killed by `Γ(γ t).1 = 0`.  Pure differentiation (chain rule along the
    curve, Leibniz) — no curvature identification yet. -/
theorem covariantSecondDeriv_at_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {γ V : ℝ → Point n × Point n} {t : ℝ}
    (hγ : ∀ τ, HasDerivAt γ (geodesicField g gi (γ τ)) τ)
    (hVar : ∀ τ, IsGeodesicVariationAt g gi γ V τ)
    (hΓ0 : ∀ i j k, christoffel g gi i j k (γ t).1 = 0) (i : Fin n) :
    covariantSecondDeriv g gi (fun τ => (γ τ).1) (fun τ => (V τ).1) t i
      = -(jacobiOperator g gi (γ t).1 (γ t).2 (V t).1 (V t).2 i)
        + ∑ j, ∑ k, (∑ a, pd (fun z => christoffel g gi i j k z) a (γ t).1 * (γ t).2 a)
                      * (γ t).2 j * (V t).1 k := by
  -- position/velocity/variation component ODEs, extracted from the phase-space ODEs `hγ`, `hVar`.
  have hx : ∀ τ, HasDerivAt (fun s => (γ s).1) ((γ τ).2) τ := by
    intro τ
    have h := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt τ (hγ τ)
    simpa [geodesicField] using h
  have hv : ∀ τ, HasDerivAt (fun s => (γ s).2) ((geodesicField g gi (γ τ)).2) τ := by
    intro τ
    have h := (ContinuousLinearMap.snd ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt τ (hγ τ)
    simpa using h
  have hval : ∀ τ, fderiv ℝ (geodesicField g gi) (γ τ) (V τ)
      = ((V τ).2, -jacobiOperator g gi (γ τ).1 (γ τ).2 (V τ).1 (V τ).2) := by
    intro τ
    have := geodesicField_fderiv_eq_jacobiOperator g gi hC (γ τ).1 (γ τ).2 (V τ).1 (V τ).2
    simpa using this
  have hξ : ∀ τ, HasDerivAt (fun s => (V s).1) ((V τ).2) τ := by
    intro τ
    have h := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt τ (hVar τ)
    rw [hval τ] at h; simpa using h
  have hη : ∀ τ, HasDerivAt (fun s => (V s).2)
      (-jacobiOperator g gi (γ τ).1 (γ τ).2 (V τ).1 (V τ).2) τ := by
    intro τ
    have h := (ContinuousLinearMap.snd ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt τ (hVar τ)
    rw [hval τ] at h; simpa using h
  have hxc : ∀ τ j, HasDerivAt (fun s => (γ s).1 j) ((γ τ).2 j) τ := fun τ j => by
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).hasFDerivAt.comp_hasDerivAt τ (hx τ)
    simpa using this
  have hvc : ∀ τ j, HasDerivAt (fun s => (γ s).2 j) ((geodesicField g gi (γ τ)).2 j) τ := fun τ j => by
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).hasFDerivAt.comp_hasDerivAt τ (hv τ)
    simpa using this
  have hξc : ∀ τ k, HasDerivAt (fun s => (V s).1 k) ((V τ).2 k) τ := fun τ k => by
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k).hasFDerivAt.comp_hasDerivAt τ (hξ τ)
    simpa using this
  have hηc : ∀ τ k, HasDerivAt (fun s => (V s).2 k)
      ((-jacobiOperator g gi (γ τ).1 (γ τ).2 (V τ).1 (V τ).2) k) τ := fun τ k => by
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k).hasFDerivAt.comp_hasDerivAt τ (hη τ)
    simpa using this
  -- the inner covariant-derivative field in clean form (velocity `x'=v` and `ξ'=η` substituted).
  have hfun : (fun s => covariantDerivAlong g gi (fun τ => (γ τ).1) (fun τ => (V τ).1) s i)
      = fun s => (V s).2 i + ∑ j, ∑ k, christoffel g gi i j k ((γ s).1) * (γ s).2 j * (V s).1 k := by
    funext s
    rw [covariantDerivAlong_apply]
    congr 1
    · exact (hξc s i).deriv
    · refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
      rw [(hxc s j).deriv]
  -- per-summand derivative of the connection term; at the centre only `(∂Γ∘x)'·v·ξ` survives.
  have hsm : ∀ j k, HasDerivAt (fun s => christoffel g gi i j k ((γ s).1) * (γ s).2 j * (V s).1 k)
      ((∑ l, pd (fun z => christoffel g gi i j k z) l (γ t).1 * (γ t).2 l) * (γ t).2 j * (V t).1 k) t := by
    intro j k
    have hA := hasDerivAt_comp_curve (fun z => christoffel g gi i j k z) (fun u => (γ u).1) ((γ t).2) t (hC i j k) (hx t)
    have hraw := (hA.mul (hvc t j)).mul (hξc t k)
    convert hraw using 1
    simp only [Pi.mul_apply, hΓ0 i j k, zero_mul, add_zero]
  have hSum : HasDerivAt (fun s => ∑ j, ∑ k, christoffel g gi i j k ((γ s).1) * (γ s).2 j * (V s).1 k)
      (∑ j, ∑ k, (∑ l, pd (fun z => christoffel g gi i j k z) l (γ t).1 * (γ t).2 l) * (γ t).2 j * (V t).1 k) t := by
    apply HasDerivAt.fun_sum
    intro j _
    apply HasDerivAt.fun_sum
    intro k _
    exact hsm j k
  have hHderiv : HasDerivAt (fun s => (V s).2 i + ∑ j, ∑ k, christoffel g gi i j k ((γ s).1) * (γ s).2 j * (V s).1 k)
      ((-jacobiOperator g gi (γ t).1 (γ t).2 (V t).1 (V t).2) i
        + ∑ j, ∑ k, (∑ l, pd (fun z => christoffel g gi i j k z) l (γ t).1 * (γ t).2 l) * (γ t).2 j * (V t).1 k) t :=
    (hηc t i).add hSum
  rw [covariantSecondDeriv_apply]
  rw [Finset.sum_eq_zero (fun j _ => Finset.sum_eq_zero (fun k _ => by simp only [hΓ0 i j k]; ring)), add_zero]
  rw [hfun, hHderiv.deriv]
  simp only [Pi.neg_apply]

/-- **The centred `∂Γ`-contraction Jacobi/curvature matching identity.**  For a lower-index-symmetric
    derivative-of-Christoffel tensor `D a b c = ∂_a Γ^i_{bc}` (`hDsymm : D a b c = D a c b`) contracted
    with the velocity `v` and the Jacobi field `ξ`, the coordinate acceleration `−jacobiOperator`
    (the `−∑(∑ D l j k ξ_l) v_j v_k` term) plus the covariant `∂Γ` correction
    (`+∑(∑ D a j k v_a) v_j ξ_k`) equals `−R(ξ,v)v` (the antisymmetrized
    `−∑(D_{μνσ}−D_{νμσ}) v_σ ξ_μ v_ν`).  Pure finite index algebra: the correction term supplies the
    `+∂Γ` half of the antisymmetrization (after `b↔c` Christoffel relabelling and `v`-symmetry) while the
    coordinate term supplies the other half. -/
theorem covariantJacobi_finset_match (D : Fin n → Fin n → Fin n → ℝ) (v ξ : Fin n → ℝ)
    (hDsymm : ∀ a b c, D a b c = D a c b) :
    -(∑ j, ∑ k, (∑ l, D l j k * ξ l) * v j * v k)
      + (∑ j, ∑ k, (∑ a, D a j k * v a) * v j * ξ k)
    = -(∑ σ, ∑ μ, ∑ ν, (D μ ν σ - D ν μ σ) * v σ * ξ μ * v ν) := by
  have hi : (∑ j, ∑ k, (∑ l, D l j k * ξ l) * v j * v k)
      = ∑ σ, ∑ μ, ∑ ν, D μ ν σ * v σ * ξ μ * v ν := by
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => ?_))
    rw [hDsymm l k j]; ring
  have hii : (∑ j, ∑ k, (∑ a, D a j k * v a) * v j * ξ k)
      = ∑ σ, ∑ μ, ∑ ν, D ν μ σ * v σ * ξ μ * v ν := by
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ =>
      Finset.sum_congr rfl (fun a _ => ?_)))
    rw [hDsymm a k j]; ring
  have hsplit : (∑ σ, ∑ μ, ∑ ν, (D μ ν σ - D ν μ σ) * v σ * ξ μ * v ν)
      = (∑ σ, ∑ μ, ∑ ν, D μ ν σ * v σ * ξ μ * v ν)
        - (∑ σ, ∑ μ, ∑ ν, D ν μ σ * v σ * ξ μ * v ν) := by
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun ν _ => ?_)
    ring
  rw [hi, hii, hsplit]; ring

/-- **The covariant Jacobi (geodesic-deviation) equation, at a Riemann-normal-coordinate centre.**
    For a geodesic `γ=(x,v)` (`hγ`) and a Jacobi field `V=(ξ,η)` (`hVar : IsGeodesicVariationAt`),
    at a base time `t` where the Christoffel symbols vanish at the base point (`Γ(γ t).1 = 0`), the
    covariant second derivative of the position variation equals minus the Riemann geodesic-deviation
    contraction:
      `D²ξ/dτ²  =  − R(ξ,γ')γ'`   (`= − riemannGeodesicDeviation g gi (γ t).1 (γ t).2 (V t).1`).
    Combines `covariantSecondDeriv_at_center` (the `∂Γ` correction), `jacobiOperator_at_center`
    (`ξ'' = −∑ ∂Γ·ξ·v·v`), and `riemannDeviation_at_center` (`R = ` antisymmetrized `∂Γ`), matched by
    the finite identity `covariantJacobi_finset_match` using Christoffel lower-symmetry
    (`christoffel_symm`, from metric symmetry `hgsymm`).  Centred case only. -/
theorem covariant_jacobi_equation_centered (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    {γ V : ℝ → Point n × Point n} {t : ℝ}
    (hγ : ∀ τ, HasDerivAt γ (geodesicField g gi (γ τ)) τ)
    (hVar : ∀ τ, IsGeodesicVariationAt g gi γ V τ)
    (hΓ0 : ∀ i j k, christoffel g gi i j k (γ t).1 = 0) :
    covariantSecondDeriv g gi (fun τ => (γ τ).1) (fun τ => (V τ).1) t
      = - riemannGeodesicDeviation g gi (γ t).1 (γ t).2 (V t).1 := by
  funext i
  rw [Pi.neg_apply]
  rw [covariantSecondDeriv_at_center g gi hC hγ hVar hΓ0 i]
  rw [congrFun (jacobiOperator_at_center g gi hΓ0 (γ t).2 (V t).1 (V t).2) i]
  rw [congrFun (riemannDeviation_at_center g gi hΓ0 (γ t).2 (V t).1) i]
  exact covariantJacobi_finset_match
    (fun a b c => pd (fun z => christoffel g gi i b c z) a (γ t).1) (γ t).2 (V t).1
    (fun a b c => by
      have h : (fun z => christoffel g gi i b c z) = (fun z => christoffel g gi i c b z) :=
        funext (fun z => christoffel_symm g gi hgsymm i b c z)
      simp only [h])

end QIQTH.ExpMap
