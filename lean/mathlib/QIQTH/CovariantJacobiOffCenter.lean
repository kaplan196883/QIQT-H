/-
  CovariantJacobiOffCenter — the OFF-CENTER covariant Jacobi (geodesic-deviation) equation.

  `CovariantJacobi.lean` proved the covariant Jacobi equation `D²ξ/dτ² = −R(ξ,v)v` ONLY at a
  Riemann-normal-coordinate CENTRE (hypothesis `hΓ0 : Γ((γ t).1) = 0`), where the live connection
  terms collapse.  This brick removes `hΓ0`: it establishes the covariant Jacobi equation along the
  WHOLE ray, with the genuine off-center connection structure (`ΓΓ`, `Γ·γ''`, `Γ·ξ'` all live).  This
  is THE wall-crossing that three prior agents stalled on, and it gates the true-kernel heat-coefficient
  `a₁ = R/6`.

  WHAT LANDS HERE:

  #1  `covariantSecondDeriv_expand` (UNCONDITIONAL off-center expansion, no `hΓ0`).  The full
      componentwise expansion of `D²ξ/dτ²` for a geodesic `γ=(x,v)` and Jacobi variation `V=(ξ,η)`:
        `(D²ξ)^i = −(jacobiOperator)^i`
                  `+ ∑_{jk} [ (∑_l ∂_l Γ^i_{jk}·v_l)·v_j·ξ_k + Γ^i_{jk}·(γ'')_j·ξ_k + Γ^i_{jk}·v_j·η_k ]`
                  `+ ∑_{jk} Γ^i_{jk}·v_j·(Dξ)_k`,
      where `−(jacobiOperator)^i = η'_i` (L2's variational ODE, off-center), the middle group is the
      τ-derivative of the inner connection term `Γ(x)·v·ξ` (chain rule `hasDerivAt_comp_curve` on `Γ∘x`,
      Leibniz on the three factors), and the last group is the outer covariant derivative of the inner
      covariant-derivative field `Dξ`.  Pure differentiation — no curvature matching, no gauge.  This is
      the honest off-center generalization of `covariantSecondDeriv_at_center` keeping ALL Γ-terms.

  #2  `covariant_jacobi_equation` (THE CRUX).  Substituting the geodesic ODE `γ'' = −∑Γ(v,v)`, the
      variational identities `ξ' = η` and `η' = −jacobiOperator`, and the inner field `Dξ = η + Γ(v,ξ)`
      into #1, and matching against the FULL Riemann geodesic-deviation `−R(ξ,v)v` (with the live `ΓΓ`
      quadratic part), gives `D²ξ/dτ² = −riemannGeodesicDeviation` along the whole ray, with NO `hΓ0`.
      The matching is the finite index identity `covariantJacobiOffCenter_finset_match`:
        * the `∂Γ`-group matches the derivative part of `R` (reuses `covariantJacobi_finset_match`);
        * the `ΓΓ`-group (from `Γ·γ''` and the double-`Γ` in `D²`) matches the quadratic part of `R`
          (pure reindexing + Christoffel lower-symmetry);
        * the `Γη`-terms cancel (Christoffel lower-symmetry).

  All regularity/gauge/dynamical inputs are carried as genuine, clearly-labelled hypotheses exactly as
  in `covariant_jacobi_equation_centered`, MINUS `hΓ0` (`hC`: Γ smooth; `hgsymm`: metric symmetric;
  `hγ`: geodesic ODE; `hVar`: Jacobi-field variational ODE).  NOT built here: Raychaudhuri (L3), the
  true-kernel existence, or `a₁ = R/6` (those are downstream of this identity).
-/
import Mathlib
import QIQTH.CovariantJacobi
import QIQTH.JacobiEquation
import QIQTH.Curvature

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset

set_option maxHeartbeats 8000000

variable {n : ℕ}

/-! ### #1 — the off-center expansion of the covariant second derivative -/

/-- **The off-center expansion of the covariant second derivative — UNCONDITIONAL (no `hΓ0`).**
    For a geodesic `γ=(x,v)` (`hγ`) and a Jacobi field `V=(ξ,η)` (`hVar`), the covariant second
    derivative of the position variation `ξ = (V·).1` along `x = (γ·).1` expands (KEEPING all
    off-center connection terms) as
      `(D²ξ)^i = −(jacobiOperator)^i`
                `+ ∑_{jk}[ (∑_l ∂_l Γ^i_{jk}(x)·v_l)·v_j·ξ_k + Γ^i_{jk}(x)·(γ'')_j·ξ_k + Γ^i_{jk}(x)·v_j·η_k ]`
                `+ ∑_{jk} Γ^i_{jk}(x)·v_j·(Dξ)_k`,
    where `−(jacobiOperator)^i = η'_i` (the off-center variational ODE), `(γ'')_j = (geodesicField γ).2 j`
    is the geodesic acceleration, and `(Dξ)_k = covariantDerivAlong g gi x ξ` is the inner covariant
    derivative.  Pure differentiation (chain rule along the curve + Leibniz) — no curvature
    identification, no RNC-centre gauge. -/
theorem covariantSecondDeriv_expand (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {γ V : ℝ → Point n × Point n} {t : ℝ}
    (hγ : ∀ τ, HasDerivAt γ (geodesicField g gi (γ τ)) τ)
    (hVar : ∀ τ, IsGeodesicVariationAt g gi γ V τ) (i : Fin n) :
    covariantSecondDeriv g gi (fun τ => (γ τ).1) (fun τ => (V τ).1) t i
      = -(jacobiOperator g gi (γ t).1 (γ t).2 (V t).1 (V t).2 i)
        + (∑ j, ∑ k,
            ((∑ l, pd (fun z => christoffel g gi i j k z) l (γ t).1 * (γ t).2 l) * (γ t).2 j * (V t).1 k
              + christoffel g gi i j k (γ t).1 * (geodesicField g gi (γ t)).2 j * (V t).1 k
              + christoffel g gi i j k (γ t).1 * (γ t).2 j * (V t).2 k))
        + ∑ j, ∑ k, christoffel g gi i j k (γ t).1 * (γ t).2 j
            * covariantDerivAlong g gi (fun τ => (γ τ).1) (fun τ => (V τ).1) t k := by
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
  -- per-summand derivative of the inner connection term (all three Leibniz pieces kept).
  have hsm : ∀ j k, HasDerivAt (fun s => christoffel g gi i j k ((γ s).1) * (γ s).2 j * (V s).1 k)
      ((∑ l, pd (fun z => christoffel g gi i j k z) l (γ t).1 * (γ t).2 l) * (γ t).2 j * (V t).1 k
        + christoffel g gi i j k (γ t).1 * (geodesicField g gi (γ t)).2 j * (V t).1 k
        + christoffel g gi i j k (γ t).1 * (γ t).2 j * (V t).2 k) t := by
    intro j k
    have hA := hasDerivAt_comp_curve (fun z => christoffel g gi i j k z) (fun u => (γ u).1) ((γ t).2) t (hC i j k) (hx t)
    have hraw := (hA.mul (hvc t j)).mul (hξc t k)
    convert hraw using 1
    simp only [Pi.mul_apply]
    ring
  have hSum : HasDerivAt (fun s => ∑ j, ∑ k, christoffel g gi i j k ((γ s).1) * (γ s).2 j * (V s).1 k)
      (∑ j, ∑ k, ((∑ l, pd (fun z => christoffel g gi i j k z) l (γ t).1 * (γ t).2 l) * (γ t).2 j * (V t).1 k
        + christoffel g gi i j k (γ t).1 * (geodesicField g gi (γ t)).2 j * (V t).1 k
        + christoffel g gi i j k (γ t).1 * (γ t).2 j * (V t).2 k)) t := by
    apply HasDerivAt.fun_sum
    intro j _
    apply HasDerivAt.fun_sum
    intro k _
    exact hsm j k
  have hHderiv : HasDerivAt
      (fun s => (V s).2 i + ∑ j, ∑ k, christoffel g gi i j k ((γ s).1) * (γ s).2 j * (V s).1 k)
      ((-jacobiOperator g gi (γ t).1 (γ t).2 (V t).1 (V t).2) i
        + ∑ j, ∑ k, ((∑ l, pd (fun z => christoffel g gi i j k z) l (γ t).1 * (γ t).2 l) * (γ t).2 j * (V t).1 k
          + christoffel g gi i j k (γ t).1 * (geodesicField g gi (γ t)).2 j * (V t).1 k
          + christoffel g gi i j k (γ t).1 * (γ t).2 j * (V t).2 k)) t :=
    (hηc t i).add hSum
  rw [covariantSecondDeriv_apply, hfun, hHderiv.deriv]
  simp only [Pi.neg_apply]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [(hxc t j).deriv]

/-! ### The finite index-matching identity for the off-center covariant Jacobi equation -/

/-- **The off-center covariant-Jacobi / Riemann matching identity (finite index algebra).**
    For a lower-index-symmetric connection `C` (`hCsymm`) and derivative-of-connection `D` (`hDsymm`),
    the off-center covariant-second-derivative expansion (`covariantSecondDeriv_expand`, after
    substituting the geodesic ODE `γ'' = −∑ C(v,v)`, `ξ' = η`, `η' = −jacobiOperator`, and the inner
    covariant derivative `Dξ = η + C(v,ξ)`) equals `−R(ξ,v)v` with the FULL Riemann tensor (live `ΓΓ`):
      * the `∂Γ`-group `(−∑(∑D ξ)vv + ∑(∑D v)vξ)` matches the derivative part of `R` — reused verbatim
        from `covariantJacobi_finset_match`;
      * the `ΓΓ`-group (`C·γ''` from the acceleration and the double-`C` from `D²`) matches the quadratic
        part of `R` — pure reindexing of a 4-fold sum (an index permutation realized by an involution)
        plus one use of Christoffel lower-symmetry;
      * the `Cη`-terms cancel (Christoffel lower-symmetry).
    No RNC-centre gauge (`Γ = 0`) is used — this is the genuine off-center identity. -/
theorem covariantJacobiOffCenter_finset_match
    (C D : Fin n → Fin n → Fin n → ℝ) (v ξ η : Fin n → ℝ) (i : Fin n)
    (hCsymm : ∀ a b c, C a b c = C a c b)
    (hDsymm : ∀ a b c, D a b c = D a c b) :
    -(∑ j, ∑ k, ((∑ l, D l j k * ξ l) * v j * v k + C i j k * η j * v k + C i j k * v j * η k))
    + (∑ j, ∑ k, ((∑ l, D l j k * v l) * v j * ξ k
                  + C i j k * (-∑ a, ∑ b, C j a b * v a * v b) * ξ k
                  + C i j k * v j * η k))
    + (∑ j, ∑ k, C i j k * v j * (η k + ∑ a, ∑ b, C k a b * v a * ξ b))
    = -(∑ σ, ∑ μ, ∑ ν, (D μ ν σ - D ν μ σ
          + ∑ l, (C i μ l * C l ν σ - C i ν l * C l μ σ)) * v σ * ξ μ * v ν) := by
  -- split the three per-summand sums into their additive atoms.
  have hP1 : (-∑ j, ∑ k, ((∑ l, D l j k * ξ l) * v j * v k + C i j k * η j * v k + C i j k * v j * η k))
      = -((∑ j, ∑ k, (∑ l, D l j k * ξ l) * v j * v k)
          + (∑ j, ∑ k, C i j k * η j * v k) + (∑ j, ∑ k, C i j k * v j * η k)) := by
    congr 1; simp only [Finset.sum_add_distrib]
  have hP2 : (∑ j, ∑ k, ((∑ l, D l j k * v l) * v j * ξ k
                  + C i j k * (-∑ a, ∑ b, C j a b * v a * v b) * ξ k + C i j k * v j * η k))
      = (∑ j, ∑ k, (∑ l, D l j k * v l) * v j * ξ k)
        + (∑ j, ∑ k, C i j k * (-∑ a, ∑ b, C j a b * v a * v b) * ξ k)
        + (∑ j, ∑ k, C i j k * v j * η k) := by
    simp only [Finset.sum_add_distrib]
  have hP3 : (∑ j, ∑ k, C i j k * v j * (η k + ∑ a, ∑ b, C k a b * v a * ξ b))
      = (∑ j, ∑ k, C i j k * v j * η k)
        + (∑ j, ∑ k, C i j k * v j * (∑ a, ∑ b, C k a b * v a * ξ b)) := by
    simp only [mul_add, Finset.sum_add_distrib]
  -- the `Cη`-terms cancel by lower-index symmetry.
  have hBC : (∑ j, ∑ k, C i j k * η j * v k) = (∑ j, ∑ k, C i j k * v j * η k) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [hCsymm i y x]; ring
  -- the `∂Γ`-group: reuse the centered derivative-part identity.
  have hAD := covariantJacobi_finset_match D v ξ hDsymm
  -- the `C·γ''` (E) term matches the first quadratic part of R.
  have hE : (∑ j, ∑ k, C i j k * (-∑ a, ∑ b, C j a b * v a * v b) * ξ k)
      = -(∑ σ, ∑ μ, ∑ ν, ∑ l, C i μ l * C l ν σ * v σ * ξ μ * v ν) := by
    have hinner : (∑ j, ∑ k, C i j k * (-∑ a, ∑ b, C j a b * v a * v b) * ξ k)
        = -(∑ j, ∑ k, ∑ a, ∑ b, C i j k * C j a b * v a * v b * ξ k) := by
      have step1 : ∀ j k, C i j k * (-∑ a, ∑ b, C j a b * v a * v b) * ξ k
          = -(∑ a, ∑ b, C i j k * C j a b * v a * v b * ξ k) := by
        intro j k
        rw [show C i j k * (-∑ a, ∑ b, C j a b * v a * v b) * ξ k
              = -((∑ a, ∑ b, C j a b * v a * v b) * (C i j k * ξ k)) from by ring, neg_inj,
            Finset.sum_mul]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun b _ => by ring)
      simp only [step1, Finset.sum_neg_distrib]
    rw [hinner]; congr 1
    rw [show (∑ j, ∑ k, ∑ a, ∑ b, C i j k * C j a b * v a * v b * ξ k)
          = ∑ p : Fin n × Fin n × Fin n × Fin n,
              C i p.1 p.2.1 * C p.1 p.2.2.1 p.2.2.2 * v p.2.2.1 * v p.2.2.2 * ξ p.2.1
        from by simp only [Fintype.sum_prod_type]]
    rw [show (∑ σ, ∑ μ, ∑ ν, ∑ l, C i μ l * C l ν σ * v σ * ξ μ * v ν)
          = ∑ p : Fin n × Fin n × Fin n × Fin n,
              C i p.2.1 p.2.2.2 * C p.2.2.2 p.2.2.1 p.1 * v p.1 * ξ p.2.1 * v p.2.2.1
        from by simp only [Fintype.sum_prod_type]]
    refine Fintype.sum_bijective
      (fun p : Fin n × Fin n × Fin n × Fin n => (p.2.2.2, p.2.1, p.2.2.1, p.1))
      (Function.Involutive.bijective
        (f := fun p : Fin n × Fin n × Fin n × Fin n => (p.2.2.2, p.2.1, p.2.2.1, p.1))
        (fun p => by rcases p with ⟨j, k, a, b⟩; rfl)) _ _ (fun p => ?_)
    rcases p with ⟨j, k, a, b⟩
    show C i j k * C j a b * v a * v b * ξ k = C i k j * C j a b * v b * ξ k * v a
    rw [hCsymm i j k]; ring
  -- the double-`C` (H) term matches the second quadratic part of R.
  have hH : (∑ j, ∑ k, C i j k * v j * (∑ a, ∑ b, C k a b * v a * ξ b))
      = (∑ σ, ∑ μ, ∑ ν, ∑ l, C i ν l * C l μ σ * v σ * ξ μ * v ν) := by
    have hinner : (∑ j, ∑ k, C i j k * v j * (∑ a, ∑ b, C k a b * v a * ξ b))
        = ∑ j, ∑ k, ∑ a, ∑ b, C i j k * v j * (C k a b * v a * ξ b) := by
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.mul_sum]
    rw [hinner]
    rw [show (∑ j, ∑ k, ∑ a, ∑ b, C i j k * v j * (C k a b * v a * ξ b))
          = ∑ p : Fin n × Fin n × Fin n × Fin n,
              C i p.1 p.2.1 * v p.1 * (C p.2.1 p.2.2.1 p.2.2.2 * v p.2.2.1 * ξ p.2.2.2)
        from by simp only [Fintype.sum_prod_type]]
    rw [show (∑ σ, ∑ μ, ∑ ν, ∑ l, C i ν l * C l μ σ * v σ * ξ μ * v ν)
          = ∑ p : Fin n × Fin n × Fin n × Fin n,
              C i p.2.2.1 p.2.2.2 * C p.2.2.2 p.2.1 p.1 * v p.1 * ξ p.2.1 * v p.2.2.1
        from by simp only [Fintype.sum_prod_type]]
    refine Fintype.sum_bijective
      (fun p : Fin n × Fin n × Fin n × Fin n => (p.2.2.1, p.2.2.2, p.1, p.2.1))
      (Function.Involutive.bijective
        (f := fun p : Fin n × Fin n × Fin n × Fin n => (p.2.2.1, p.2.2.2, p.1, p.2.1))
        (fun p => by rcases p with ⟨j, k, a, b⟩; rfl)) _ _ (fun p => ?_)
    rcases p with ⟨j, k, a, b⟩
    show C i j k * v j * (C k a b * v a * ξ b) = C i j k * C k b a * v a * ξ b * v j
    rw [hCsymm k a b]; ring
  -- split the quadratic part of R into its two pieces.
  have hG3 : (-(∑ σ, ∑ μ, ∑ ν, (∑ l, (C i μ l * C l ν σ - C i ν l * C l μ σ)) * v σ * ξ μ * v ν))
      = -(∑ σ, ∑ μ, ∑ ν, ∑ l, C i μ l * C l ν σ * v σ * ξ μ * v ν)
        + (∑ σ, ∑ μ, ∑ ν, ∑ l, C i ν l * C l μ σ * v σ * ξ μ * v ν) := by
    have key : (∑ σ, ∑ μ, ∑ ν, (∑ l, (C i μ l * C l ν σ - C i ν l * C l μ σ)) * v σ * ξ μ * v ν)
        = (∑ σ, ∑ μ, ∑ ν, ∑ l, C i μ l * C l ν σ * v σ * ξ μ * v ν)
          - (∑ σ, ∑ μ, ∑ ν, ∑ l, C i ν l * C l μ σ * v σ * ξ μ * v ν) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun μ _ => ?_)
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun ν _ => ?_)
      rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    rw [key]; ring
  -- split R into its derivative part and its quadratic part.
  have hR : (-(∑ σ, ∑ μ, ∑ ν, (D μ ν σ - D ν μ σ
          + ∑ l, (C i μ l * C l ν σ - C i ν l * C l μ σ)) * v σ * ξ μ * v ν))
      = -(∑ σ, ∑ μ, ∑ ν, (D μ ν σ - D ν μ σ) * v σ * ξ μ * v ν)
        + (-(∑ σ, ∑ μ, ∑ ν, (∑ l, (C i μ l * C l ν σ - C i ν l * C l μ σ)) * v σ * ξ μ * v ν)) := by
    have e2 : ∀ σ μ ν, (D μ ν σ - D ν μ σ
            + ∑ l, (C i μ l * C l ν σ - C i ν l * C l μ σ)) * v σ * ξ μ * v ν
        = (D μ ν σ - D ν μ σ) * v σ * ξ μ * v ν
          + (∑ l, (C i μ l * C l ν σ - C i ν l * C l μ σ)) * v σ * ξ μ * v ν := by
      intro σ μ ν; ring
    simp only [e2, Finset.sum_add_distrib]
    ring
  linarith [hP1, hP2, hP3, hBC, hAD, hE, hH, hG3, hR]

/-! ### #2 — the OFF-CENTER covariant Jacobi equation (the crux) -/

/-- **The covariant Jacobi (geodesic-deviation) equation, OFF-CENTER — along the whole ray.**
    For a geodesic `γ=(x,v)` (`hγ`) and a Jacobi field `V=(ξ,η)` (`hVar : IsGeodesicVariationAt`), with
    NO Riemann-normal-coordinate gauge, the covariant second derivative of the position variation equals
    minus the (FULL) Riemann geodesic-deviation contraction:
      `D²ξ/dτ² = − R(ξ,γ')γ'`   (`= − riemannGeodesicDeviation g gi (γ t).1 (γ t).2 (V t).1`).
    Combines the off-center expansion `covariantSecondDeriv_expand` (all connection terms live) with the
    geodesic ODE (`γ'' = −∑ Γ(v,v)`, definitional in `geodesicField`), `ξ' = η`, `η' = −jacobiOperator`,
    and the inner covariant derivative `Dξ = η + Γ(v,ξ)`, matched to the full Riemann tensor by the finite
    identity `covariantJacobiOffCenter_finset_match` (Christoffel lower-symmetry `christoffel_symm`).
    This removes the `hΓ0` hypothesis of `covariant_jacobi_equation_centered`. -/
theorem covariant_jacobi_equation (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    {γ V : ℝ → Point n × Point n} {t : ℝ}
    (hγ : ∀ τ, HasDerivAt γ (geodesicField g gi (γ τ)) τ)
    (hVar : ∀ τ, IsGeodesicVariationAt g gi γ V τ) :
    covariantSecondDeriv g gi (fun τ => (γ τ).1) (fun τ => (V τ).1) t
      = - riemannGeodesicDeviation g gi (γ t).1 (γ t).2 (V t).1 := by
  -- component ODEs needed to expand the inner covariant derivative `Dξ`.
  have hx : ∀ τ, HasDerivAt (fun s => (γ s).1) ((γ τ).2) τ := by
    intro τ
    have h := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt τ (hγ τ)
    simpa [geodesicField] using h
  have hval : ∀ τ, fderiv ℝ (geodesicField g gi) (γ τ) (V τ)
      = ((V τ).2, -jacobiOperator g gi (γ τ).1 (γ τ).2 (V τ).1 (V τ).2) := by
    intro τ
    have := geodesicField_fderiv_eq_jacobiOperator g gi hC (γ τ).1 (γ τ).2 (V τ).1 (V τ).2
    simpa using this
  have hξ : ∀ τ, HasDerivAt (fun s => (V s).1) ((V τ).2) τ := by
    intro τ
    have h := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt τ (hVar τ)
    rw [hval τ] at h; simpa using h
  have hxc : ∀ τ j, HasDerivAt (fun s => (γ s).1 j) ((γ τ).2 j) τ := fun τ j => by
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).hasFDerivAt.comp_hasDerivAt τ (hx τ)
    simpa using this
  have hξc : ∀ τ k, HasDerivAt (fun s => (V s).1 k) ((V τ).2 k) τ := fun τ k => by
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k).hasFDerivAt.comp_hasDerivAt τ (hξ τ)
    simpa using this
  -- the inner covariant derivative in explicit (substituted) form.
  have hcov : ∀ k, covariantDerivAlong g gi (fun τ => (γ τ).1) (fun τ => (V τ).1) t k
      = (V t).2 k + ∑ a, ∑ b, christoffel g gi k a b (γ t).1 * (γ t).2 a * (V t).1 b := by
    intro k
    rw [covariantDerivAlong_apply]
    congr 1
    · exact (hξc t k).deriv
    · refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [(hxc t a).deriv]
  funext i
  rw [Pi.neg_apply, covariantSecondDeriv_expand g gi hC hγ hVar i]
  rw [show (∑ j, ∑ k, christoffel g gi i j k (γ t).1 * (γ t).2 j
              * covariantDerivAlong g gi (fun τ => (γ τ).1) (fun τ => (V τ).1) t k)
        = ∑ j, ∑ k, christoffel g gi i j k (γ t).1 * (γ t).2 j
            * ((V t).2 k + ∑ a, ∑ b, christoffel g gi k a b (γ t).1 * (γ t).2 a * (V t).1 b)
      from Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => by rw [hcov k]))]
  exact covariantJacobiOffCenter_finset_match
    (fun a b c => christoffel g gi a b c (γ t).1)
    (fun a b c => pd (fun z => christoffel g gi i b c z) a (γ t).1)
    (γ t).2 (V t).1 (V t).2 i
    (fun a b c => christoffel_symm g gi hgsymm a b c (γ t).1)
    (fun a b c => by
      have h : (fun z => christoffel g gi i b c z) = (fun z => christoffel g gi i c b z) :=
        funext (fun z => christoffel_symm g gi hgsymm i b c z)
      simp only [h])

end QIQTH.ExpMap
