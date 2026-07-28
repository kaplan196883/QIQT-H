/-
  ParallelOrthonormal — ORTHONORMALITY PRESERVATION under parallel transport (Phase M2b-2a).

  MATRIX_JACOBI_PLAN.md, off-radial matrix-Jacobi campaign.  Direct corollary of the M2b-1
  isometry `QIQTH.ParallelTransport.parallel_metricInner_const`: for parallel vector fields the
  metric pairing `⟨e_i,e_j⟩_g(τ) := ∑_{ab} g_{ab}(γ τ)·e_i^a(τ)·e_j^b(τ)` has derivative `0` at
  EVERY `τ`, hence is CONSTANT in `τ` (Mathlib `is_const_of_deriv_eq_zero`).  Therefore a parallel
  frame that is orthonormal at one point (`τ = 0`) stays orthonormal at every `τ`:

      `∑_{ab} g_{ab}(γ τ)·e_i^a(τ)·e_j^b(τ) = δ_{ij}    for all τ`.

  This DISCHARGES the `hortho` (orthonormal-frame) hypothesis carried by `frame_jacobi_equation`
  and the geodesic Raychaudhuri equation, GIVEN parallel transport + initial orthonormality.

  WHAT IS **NOT** HERE (honest scope):
    • no parallel-frame EXISTENCE — the linear frame ODE `e_i' = −Γ(γ)(γ',e_i)` is not solved
      (M2b-2); the parallel fields `e` are carried as hypotheses (`he`/`hep`), not constructed.
    • no `Ỹ'' = −R̃ Ỹ` and no `tr R̃ = Ric` (M2b-3 / M2b-4).
    • no heat-kernel `a₁ = R/6` (M6).
  Only the preservation identity `⟨e_i,e_j⟩_g(τ) = δ_{ij}` (from constancy of the pairing) lands here.
-/
import Mathlib
import QIQTH.ParallelTransport

namespace QIQTH.ParallelTransport

open QIQTH.Curvature QIQTH.ExpMap Finset

variable {n : ℕ}

/-- **A parallel frame orthonormal at one point stays orthonormal.**  For a symmetric, invertible,
    `C¹` metric `g` and a FAMILY `e : Fin n → ℝ → Point n` of vector fields that are each PARALLEL
    along `γ` (`he`/`hep`), the metric pairing `⟨e_i,e_j⟩_g(τ)` is constant in `τ` (M2b-1 isometry
    `parallel_metricInner_const` gives derivative `0` everywhere; `is_const_of_deriv_eq_zero` gives
    constancy).  Hence initial orthonormality `h0` at `τ = 0` propagates to all `τ`.

    The hypotheses are all INPUTS: `h0` is orthonormality at the SINGLE point `τ = 0`, and
    `he`/`hep` are the regularity/parallel conditions; the ALL-`τ` orthonormality is DERIVED. -/
theorem parallel_orthonormal_preserved
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hsymm : ∀ y a b, g y a b = g y b a)
    (γ γ' : ℝ → Point n)
    (e e' : Fin n → ℝ → Point n)
    (hinv : ∀ τ a b, (∑ σ, g (γ τ) a σ * gi (γ τ) σ b) = if a = b then 1 else 0)
    (hγ : ∀ τ, HasDerivAt γ (γ' τ) τ)
    (he : ∀ i τ k, HasDerivAt (fun s => e i s k) (e' i τ k) τ)
    (hep : ∀ i τ k, e' i τ k = -∑ j, ∑ l, christoffel g gi k j l (γ τ) * γ' τ j * e i τ l)
    (h0 : ∀ i j, (∑ a, ∑ b, g (γ 0) a b * e i 0 a * e j 0 b) = if i = j then (1 : ℝ) else 0)
    (τ : ℝ) (i j : Fin n) :
    (∑ a, ∑ b, g (γ τ) a b * e i τ a * e j τ b) = if i = j then (1 : ℝ) else 0 := by
  -- M2b-1 isometry: the pairing ⟨e_i,e_j⟩_g has derivative 0 at every point.
  have hderiv : ∀ s, HasDerivAt (fun t => ∑ a, ∑ b, g (γ t) a b * e i t a * e j t b) 0 s :=
    fun s => parallel_metricInner_const g gi hg hsymm γ γ' (e i) (e' i) (e j) (e' j)
      hinv hγ (he i) (he j) (hep i) (hep j) s
  -- Derivative 0 everywhere ⇒ the pairing is constant in τ, so it equals its value at τ = 0.
  have hc := is_const_of_deriv_eq_zero
    (fun s => (hderiv s).differentiableAt) (fun s => (hderiv s).deriv) τ 0
  simpa using hc.trans (h0 i j)

end QIQTH.ParallelTransport
