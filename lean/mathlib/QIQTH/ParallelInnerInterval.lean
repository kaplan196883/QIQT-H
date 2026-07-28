/-
  ParallelInnerInterval — the g-inner product of two parallel-transported vectors is CONSTANT
  on the whole transport interval `Ioo a b`.

  Building on the pointwise `parallel_metricInner_const_at` (which supplies `d/du⟨e,f⟩_g = 0`
  at each interior point `u` of the interval), we upgrade to a genuine interval statement:
  `P u := ∑ p q, g (γ u) p q * e u p * f u q` has vanishing derivative at every `u ∈ Ioo a b`,
  and `Ioo a b` is open and preconnected, so `P` is literally constant there
  (`IsOpen.is_const_of_deriv_eq_zero`).

  WHY: a locally-existing parallel transport (Picard–Lindelöf on an interval) supplies the
  transport ODE only on that interval.  Applied to an orthonormal initial condition at an
  interior point `t`, this constancy gives orthonormality on the whole transport neighbourhood.

  This is a step `b` toward the frame construction; it is NOT the frame itself and NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ParallelMetricInnerAt

namespace QIQTH.ParallelTransport

open QIQTH.Curvature QIQTH.ExpMap Finset Set

variable {n : ℕ}

set_option maxHeartbeats 800000

/-- The g-inner product of two parallel-transported vector fields `e`, `f` along `γ` is constant
on the transport interval `Ioo a b`: for any interior points `s`, `t`,
`⟨e s, f s⟩_{g(γ s)} = ⟨e t, f t⟩_{g(γ t)}`.

Each interior point contributes `d/du ⟨e u, f u⟩ = 0` via `parallel_metricInner_const_at`, and
`Ioo a b` is open + preconnected, so the inner product is literally constant on it
(`IsOpen.is_const_of_deriv_eq_zero`). -/
theorem parallelPair_metricInner_eq_on_Ioo (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hsymm : ∀ y a b, g y a b = g y b a)
    (γ γ' e e' f f' : ℝ → Point n) {a b t : ℝ} (ht : t ∈ Set.Ioo a b)
    (hinv : ∀ s ∈ Set.Ioo a b, ∀ p q,
      (∑ σ, g (γ s) p σ * gi (γ s) σ q) = if p = q then 1 else 0)
    (hγ : ∀ s ∈ Set.Ioo a b, HasDerivAt γ (γ' s) s)
    (he : ∀ s ∈ Set.Ioo a b, ∀ i, HasDerivAt (fun u => e u i) (e' s i) s)
    (hf : ∀ s ∈ Set.Ioo a b, ∀ i, HasDerivAt (fun u => f u i) (f' s i) s)
    (hep : ∀ s ∈ Set.Ioo a b, ∀ i,
      e' s i = -∑ j, ∑ k, christoffel g gi i j k (γ s) * γ' s j * e s k)
    (hfp : ∀ s ∈ Set.Ioo a b, ∀ i,
      f' s i = -∑ j, ∑ k, christoffel g gi i j k (γ s) * γ' s j * f s k)
    (s : ℝ) (hs : s ∈ Set.Ioo a b) :
    (∑ p, ∑ q, g (γ s) p q * e s p * f s q)
      = (∑ p, ∑ q, g (γ t) p q * e t p * f t q) := by
  set P : ℝ → ℝ := fun u => ∑ p, ∑ q, g (γ u) p q * e u p * f u q with hP
  -- Pointwise: `P` has derivative `0` at every interior point of the interval.
  have hderiv : ∀ u ∈ Set.Ioo a b, HasDerivAt P 0 u := by
    intro u hu
    exact parallel_metricInner_const_at g gi hg hsymm γ γ' e e' f f'
      (hinv u hu) (hγ u hu) (he u hu) (hf u hu) (hep u hu) (hfp u hu)
  -- Hence `P` is differentiable on `Ioo a b` and its `deriv` vanishes there.
  have hdiffOn : DifferentiableOn ℝ P (Set.Ioo a b) := fun u hu =>
    (hderiv u hu).differentiableAt.differentiableWithinAt
  have hderiv0 : Set.EqOn (deriv P) 0 (Set.Ioo a b) := by
    intro u hu
    simp [(hderiv u hu).deriv]
  -- `Ioo a b` is open and preconnected, so `P` is constant on it.
  exact (isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiffOn hderiv0 hs ht)

end QIQTH.ParallelTransport
