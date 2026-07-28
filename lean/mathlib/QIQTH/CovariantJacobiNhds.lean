/-
  CovariantJacobiNhds — NEIGHBORHOOD localization of the off-center covariant Jacobi machinery.

  `CovariantJacobiOffCenter.lean` proved the off-center covariant second-derivative expansion
  (`covariantSecondDeriv_expand`) and the off-center covariant Jacobi equation
  (`covariant_jacobi_equation`) under GLOBAL hypotheses `∀ τ, HasDerivAt γ …` and
  `∀ τ, IsGeodesicVariationAt g gi γ V τ`.  The exp-flow, however, only supplies the geodesic ODE
  on an interval (`Ioo (-2) 2`) and the variation ODE on `[0,1]` — i.e. only on a NEIGHBORHOOD of an
  interior point `t`, not for all `τ`.

  WHAT LANDS HERE:

  #1  `covariantSecondDeriv_expand_nhds` — identical statement and RHS to `covariantSecondDeriv_expand`
      but with the two hypotheses weakened to `∀ᶠ τ in nhds t, …`.  The per-`τ` component ODEs become
      `Filter.Eventually` facts (via `filter_upwards`); AT-`t` uses go through `.self_of_nhds`; the
      global `funext` field-identity `hfun` becomes an `EventuallyEq` (`hfun_ev`), and the final
      differentiation rewrites the ray `deriv` across it via `Filter.EventuallyEq.deriv_eq`.

  #2  `covariant_jacobi_equation_nhds` — identical statement and RHS to `covariant_jacobi_equation`
      but with the same two `∀ᶠ … in nhds t` hypotheses; proved by calling
      `covariantSecondDeriv_expand_nhds` in place of `covariantSecondDeriv_expand` and reusing the
      finite index-matching identity `covariantJacobiOffCenter_finset_match` verbatim.

  This is the bridge that lets the covariant/coordinate Jacobi machinery apply to the exp-flow.  It is
  still the covariant/coordinate layer: it does NOT prove the frame identity `B'' = −R̃ B`, the trace
  `tr R̃ = Ric`, or the heat-coefficient `a₁ = R/6` (all downstream).
-/
import Mathlib
import QIQTH.CovariantJacobiOffCenter

namespace QIQTH.ExpMap

open QIQTH.Curvature QIQTH.Geodesic
open Finset

set_option maxHeartbeats 8000000

variable {n : ℕ}

/-! ### #1 — the off-center expansion, localized to a neighborhood of `t` -/

/-- **The off-center expansion of the covariant second derivative — localized (`∀ᶠ … in 𝓝 t`).**
    Identical to `covariantSecondDeriv_expand`, but the geodesic ODE `hγ` and the Jacobi-variation ODE
    `hVar` are only assumed on a NEIGHBORHOOD of `t` (the form the exp-flow supplies).  Pure
    differentiation localized: the component ODEs are `Filter.Eventually` facts, the inner
    covariant-derivative field agrees with its explicit form `EventuallyEq`, and the ray derivative at
    `t` is rewritten across that `EventuallyEq`. -/
theorem covariantSecondDeriv_expand_nhds (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {γ V : ℝ → Point n × Point n} {t : ℝ}
    (hγ : ∀ᶠ τ in nhds t, HasDerivAt γ (geodesicField g gi (γ τ)) τ)
    (hVar : ∀ᶠ τ in nhds t, IsGeodesicVariationAt g gi γ V τ) (i : Fin n) :
    covariantSecondDeriv g gi (fun τ => (γ τ).1) (fun τ => (V τ).1) t i
      = -(jacobiOperator g gi (γ t).1 (γ t).2 (V t).1 (V t).2 i)
        + (∑ j, ∑ k,
            ((∑ l, pd (fun z => christoffel g gi i j k z) l (γ t).1 * (γ t).2 l) * (γ t).2 j * (V t).1 k
              + christoffel g gi i j k (γ t).1 * (geodesicField g gi (γ t)).2 j * (V t).1 k
              + christoffel g gi i j k (γ t).1 * (γ t).2 j * (V t).2 k))
        + ∑ j, ∑ k, christoffel g gi i j k (γ t).1 * (γ t).2 j
            * covariantDerivAlong g gi (fun τ => (γ τ).1) (fun τ => (V τ).1) t k := by
  -- position/velocity/variation component ODEs, now as `Filter.Eventually` facts near `t`.
  have hx : ∀ᶠ τ in nhds t, HasDerivAt (fun s => (γ s).1) ((γ τ).2) τ := by
    filter_upwards [hγ] with τ hγτ
    have h := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt τ hγτ
    simpa [geodesicField] using h
  have hv : ∀ᶠ τ in nhds t, HasDerivAt (fun s => (γ s).2) ((geodesicField g gi (γ τ)).2) τ := by
    filter_upwards [hγ] with τ hγτ
    have h := (ContinuousLinearMap.snd ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt τ hγτ
    simpa using h
  -- `hval` is unconditional (comes only from `hC`) — keep it `∀ τ`.
  have hval : ∀ τ, fderiv ℝ (geodesicField g gi) (γ τ) (V τ)
      = ((V τ).2, -jacobiOperator g gi (γ τ).1 (γ τ).2 (V τ).1 (V τ).2) := by
    intro τ
    have := geodesicField_fderiv_eq_jacobiOperator g gi hC (γ τ).1 (γ τ).2 (V τ).1 (V τ).2
    simpa using this
  have hξ : ∀ᶠ τ in nhds t, HasDerivAt (fun s => (V s).1) ((V τ).2) τ := by
    filter_upwards [hVar] with τ hVarτ
    have h := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt τ hVarτ
    rw [hval τ] at h; simpa using h
  have hη : ∀ᶠ τ in nhds t, HasDerivAt (fun s => (V s).2)
      (-jacobiOperator g gi (γ τ).1 (γ τ).2 (V τ).1 (V τ).2) τ := by
    filter_upwards [hVar] with τ hVarτ
    have h := (ContinuousLinearMap.snd ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt τ hVarτ
    rw [hval τ] at h; simpa using h
  have hxc : ∀ᶠ τ in nhds t, ∀ j, HasDerivAt (fun s => (γ s).1 j) ((γ τ).2 j) τ := by
    filter_upwards [hx] with τ hxτ
    intro j
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).hasFDerivAt.comp_hasDerivAt τ hxτ
    simpa using this
  have hvc : ∀ᶠ τ in nhds t, ∀ j, HasDerivAt (fun s => (γ s).2 j) ((geodesicField g gi (γ τ)).2 j) τ := by
    filter_upwards [hv] with τ hvτ
    intro j
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).hasFDerivAt.comp_hasDerivAt τ hvτ
    simpa using this
  have hξc : ∀ᶠ τ in nhds t, ∀ k, HasDerivAt (fun s => (V s).1 k) ((V τ).2 k) τ := by
    filter_upwards [hξ] with τ hξτ
    intro k
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k).hasFDerivAt.comp_hasDerivAt τ hξτ
    simpa using this
  have hηc : ∀ᶠ τ in nhds t, ∀ k, HasDerivAt (fun s => (V s).2 k)
      ((-jacobiOperator g gi (γ τ).1 (γ τ).2 (V τ).1 (V τ).2) k) τ := by
    filter_upwards [hη] with τ hnτ
    intro k
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k).hasFDerivAt.comp_hasDerivAt τ hnτ
    simpa using this
  -- AT-`t` versions of the component ODEs (self of nhds).
  have hx_t := hx.self_of_nhds
  have hvc_t := hvc.self_of_nhds
  have hξc_t := hξc.self_of_nhds
  have hηc_t := hηc.self_of_nhds
  have hxc_t := hxc.self_of_nhds
  -- the inner covariant-derivative field agrees with its explicit form on a neighborhood of `t`.
  have hfun_ev : (fun s => covariantDerivAlong g gi (fun τ => (γ τ).1) (fun τ => (V τ).1) s i)
      =ᶠ[nhds t] fun s => (V s).2 i
        + ∑ j, ∑ k, christoffel g gi i j k ((γ s).1) * (γ s).2 j * (V s).1 k := by
    filter_upwards [hξc, hxc] with s hξcs hxcs
    rw [covariantDerivAlong_apply]
    congr 1
    · exact (hξcs i).deriv
    · refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
      rw [(hxcs j).deriv]
  -- per-summand derivative of the inner connection term (AT `t`, all three Leibniz pieces).
  have hsm : ∀ j k, HasDerivAt (fun s => christoffel g gi i j k ((γ s).1) * (γ s).2 j * (V s).1 k)
      ((∑ l, pd (fun z => christoffel g gi i j k z) l (γ t).1 * (γ t).2 l) * (γ t).2 j * (V t).1 k
        + christoffel g gi i j k (γ t).1 * (geodesicField g gi (γ t)).2 j * (V t).1 k
        + christoffel g gi i j k (γ t).1 * (γ t).2 j * (V t).2 k) t := by
    intro j k
    have hA := hasDerivAt_comp_curve (fun z => christoffel g gi i j k z) (fun u => (γ u).1) ((γ t).2) t (hC i j k) hx_t
    have hraw := (hA.mul (hvc_t j)).mul (hξc_t k)
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
    (hηc_t i).add hSum
  rw [covariantSecondDeriv_apply, hfun_ev.deriv_eq, hHderiv.deriv]
  simp only [Pi.neg_apply]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [(hxc_t j).deriv]

/-! ### #2 — the off-center covariant Jacobi equation, localized to a neighborhood of `t` -/

/-- **The covariant Jacobi (geodesic-deviation) equation, OFF-CENTER, localized (`∀ᶠ … in 𝓝 t`).**
    Identical to `covariant_jacobi_equation`, but the geodesic ODE `hγ` and the Jacobi-variation ODE
    `hVar` are only assumed on a NEIGHBORHOOD of `t`.  Proved by feeding the localized expansion
    `covariantSecondDeriv_expand_nhds` into the (unchanged) finite index-matching identity
    `covariantJacobiOffCenter_finset_match`. -/
theorem covariant_jacobi_equation_nhds (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    {γ V : ℝ → Point n × Point n} {t : ℝ}
    (hγ : ∀ᶠ τ in nhds t, HasDerivAt γ (geodesicField g gi (γ τ)) τ)
    (hVar : ∀ᶠ τ in nhds t, IsGeodesicVariationAt g gi γ V τ) :
    covariantSecondDeriv g gi (fun τ => (γ τ).1) (fun τ => (V τ).1) t
      = - riemannGeodesicDeviation g gi (γ t).1 (γ t).2 (V t).1 := by
  -- component ODEs needed to expand the inner covariant derivative `Dξ` (AT `t`).
  have hx : ∀ᶠ τ in nhds t, HasDerivAt (fun s => (γ s).1) ((γ τ).2) τ := by
    filter_upwards [hγ] with τ hγτ
    have h := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt τ hγτ
    simpa [geodesicField] using h
  have hval : ∀ τ, fderiv ℝ (geodesicField g gi) (γ τ) (V τ)
      = ((V τ).2, -jacobiOperator g gi (γ τ).1 (γ τ).2 (V τ).1 (V τ).2) := by
    intro τ
    have := geodesicField_fderiv_eq_jacobiOperator g gi hC (γ τ).1 (γ τ).2 (V τ).1 (V τ).2
    simpa using this
  have hξ : ∀ᶠ τ in nhds t, HasDerivAt (fun s => (V s).1) ((V τ).2) τ := by
    filter_upwards [hVar] with τ hVarτ
    have h := (ContinuousLinearMap.fst ℝ (Point n) (Point n)).hasFDerivAt.comp_hasDerivAt τ hVarτ
    rw [hval τ] at h; simpa using h
  have hxc : ∀ᶠ τ in nhds t, ∀ j, HasDerivAt (fun s => (γ s).1 j) ((γ τ).2 j) τ := by
    filter_upwards [hx] with τ hxτ
    intro j
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).hasFDerivAt.comp_hasDerivAt τ hxτ
    simpa using this
  have hξc : ∀ᶠ τ in nhds t, ∀ k, HasDerivAt (fun s => (V s).1 k) ((V τ).2 k) τ := by
    filter_upwards [hξ] with τ hξτ
    intro k
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) k).hasFDerivAt.comp_hasDerivAt τ hξτ
    simpa using this
  have hxc_t := hxc.self_of_nhds
  have hξc_t := hξc.self_of_nhds
  -- the inner covariant derivative in explicit (substituted) form, AT `t`.
  have hcov : ∀ k, covariantDerivAlong g gi (fun τ => (γ τ).1) (fun τ => (V τ).1) t k
      = (V t).2 k + ∑ a, ∑ b, christoffel g gi k a b (γ t).1 * (γ t).2 a * (V t).1 b := by
    intro k
    rw [covariantDerivAlong_apply]
    congr 1
    · exact (hξc_t k).deriv
    · refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [(hxc_t a).deriv]
  funext i
  rw [Pi.neg_apply, covariantSecondDeriv_expand_nhds g gi hC hγ hVar i]
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
