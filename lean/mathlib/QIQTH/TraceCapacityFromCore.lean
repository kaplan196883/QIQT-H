/-
  W4 (TYPE_II_TRACE_PLAN.md) — THE PAYOFF: the capacity interfaces fed by the CONSTRUCTED trace.

  The ladder's endpoint. The dual-weight trace τ₀ built in W1–W3b (dual action + log-clock density + monomial
  formula + traciality + positivity) now INSTANTIATES the two capacity interfaces that were, until today, bare
  hypotheses:
  • `phase5_from_core_trace` — a `Phase5Master` certificate whose **nonnegative JLMS remainder is REALIZED as the
    constructed trace of a star-square element**, `remainder := τ₀(r*·r) ≥ 0` (W3b's positivity theorem powering
    the certificate field that was previously posited);
  • `traceCapacity_from_core` — a `TraceCapacity` certificate whose **bound is PROVEN, not assumed**: the
    renormalized-entropy slack `Q − S_ren` is the constructed `τ₀(r*·r)`, so `S_ren ≤ Q` follows from W3b.
  Plus `CoreDensity` (positive, normalized star-square core densities) and the CARRIED
  **`DualWeightTraceExtension`** class — the honest interface for the full CPW von Neumann trace (normal,
  semifinite, faithful, extending τ₀, same dual scaling, tracial): a named typeclass hypothesis, NEVER an axiom
  (the normal-weight/affiliated-operator theory it needs is the genuine remaining frontier; the core-approximation
  layer of the consult is subsumed in its `extends_core` clause pending a vN state type).

  ⚠ Honest scope — THE WALL IS NOT CROSSED: what is constructed is the dual-weight trace ON THE ALGEBRAIC CORE
  with its three trace laws exact; the von Neumann closure, the continuum count, and the black-hole matching
  remain carried/cited. NOT QG. Axiom-free, std-3.
-/
import Mathlib
import QIQTH.EigenCore
import QIQTH.FQBoundCGP
import QIQTH.QG.CpsuvEscape

namespace QIQTH.TypeIITrace

open MeasureTheory

variable {A : Type*} [Mul A] [Star A]

/-- **A core density**: a normalized star-square eigen-core element `ρ = x*·x` (positive by W3b), with unit
    trace mass. -/
structure CoreDensity (A : Type*) [Mul A] [Star A] (ω : A → ℂ) where
  /-- the underlying eigen-core element -/
  x : EigenTerm A
  /-- matter positivity at `x` (carried modular-matter input) -/
  hpos : 0 ≤ (ω (Star.star x.a * x.a)).re ∧ (ω (Star.star x.a * x.a)).im = 0
  /-- unit trace mass -/
  mass_one : ((x.star.mul x).tau ω).re = 1

/-- A core density's trace is the (real, nonnegative) value 1 — the constructed trace normalizes it. -/
theorem CoreDensity.tau_nonneg (ω : A → ℂ) (ρ : CoreDensity A ω) :
    0 ≤ ((ρ.x.star.mul ρ.x).tau ω).re :=
  (eigen_tau_star_mul_nonneg ω ρ.x ρ.hpos).1

/-- **W4a — the Phase-5 certificate FED BY THE CONSTRUCTED TRACE.** The JLMS remainder — previously a bare
    posited field — is REALIZED as the dual-weight trace of a star-square core element, `remainder := τ₀(r*·r)`,
    with its nonnegativity supplied by W3b's positivity THEOREM. The JLMS balance (the area/calibration content)
    stays the explicit carried input — exactly the honest boundary. -/
noncomputable def phase5_from_core_trace {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StandardSubspace H) (ξ : H) (SvN areaTerm : ℝ) (ω : A → ℂ) (r : EigenTerm A)
    (hpos : 0 ≤ (ω (Star.star r.a * r.a)).re ∧ (ω (Star.star r.a * r.a)).im = 0)
    (hbalance : SvN + QIQTH.cgpEntropy S ξ
      + ((r.star.mul r).tau ω).re = areaTerm) :
    QIQTH.Phase5Master S ξ SvN areaTerm where
  remainder := ((r.star.mul r).tau ω).re
  remainder_nonneg := (eigen_tau_star_mul_nonneg ω r hpos).1
  jlms_balance := hbalance

/-- **W4b — the trace-capacity certificate with a PROVEN bound.** The renormalized-entropy slack is the
    constructed trace of a star-square element: `S_ren := Q − τ₀(r*·r)`, so `S_ren ≤ Q` is a THEOREM (W3b
    positivity), not an assumption. The identification of `S_ren` with the capacity-minus-remainder bookkeeping
    is the JLMS shape; computing it from a density's logarithm needs the carried vN extension. -/
noncomputable def traceCapacity_from_core (ClockFrame : Type) (ω : A → ℂ) (r : EigenTerm A)
    (hpos : 0 ≤ (ω (Star.star r.a * r.a)).re ∧ (ω (Star.star r.a * r.a)).im = 0)
    (Q : ℝ) : QIQTH.QG.TraceCapacity ClockFrame where
  Sren := Q - ((r.star.mul r).tau ω).re
  Q := Q
  bound := by linarith [(eigen_tau_star_mul_nonneg ω r hpos).1]

/-- **CARRIED — the full CPW von Neumann extension** (the genuine remaining frontier: normal weights, affiliated
    operators, semifiniteness — theory Mathlib does not yet have). A named typeclass hypothesis, NEVER an axiom:
    an ambient carrier with a MULTIPLICATIVE embedding of the eigen-core and a real trace functional extending
    the constructed core trace, with the same `e^{−s}` dual scaling and full traciality.
    ⚠ K3 HYGIENE (the keystone campaign): the previous shape (no `embed_mul`) was satisfiable by an abelian
    collapse witness (`M = ℂ`, `τ = re`, `embed = tau ω`) for ANY algebra — a vacuous interface. The
    multiplicativity requirement kills that witness (the core trace is not multiplicative), restoring the
    intended strength. Instantiating it = crossing the wall's remaining half. -/
class DualWeightTraceExtension (A : Type*) [Mul A] [Star A] (ω : A → ℂ) : Prop where
  exists_extension : ∃ (M : Type) (_ : Mul M) (embed : EigenTerm A → M)
    (τ : M → ℝ) (θ : ℝ → M → M),
    (∀ x : EigenTerm A, τ (embed x) = (x.tau ω).re) ∧
    (∀ x y : EigenTerm A, embed (x.mul y) = embed x * embed y) ∧
    (∀ (s : ℝ) (m : M), τ (θ s m) = Real.exp (-s) * τ m) ∧
    (∀ m₁ m₂ : M, τ (m₁ * m₂) = τ (m₂ * m₁))

/-- Under the carried extension, the extended trace inherits the core normalization: any core density keeps unit
    mass in the ambient trace. -/
theorem extension_preserves_density_mass (ω : A → ℂ) [h : DualWeightTraceExtension A ω]
    (ρ : CoreDensity A ω) :
    ∃ (M : Type) (_ : Mul M) (embed : EigenTerm A → M) (τ : M → ℝ),
      τ (embed (ρ.x.star.mul ρ.x)) = 1 := by
  obtain ⟨M, hM, embed, τ, θ, hext, _, _, _⟩ := h.exists_extension
  exact ⟨M, hM, embed, τ, by rw [hext]; exact ρ.mass_one⟩

end QIQTH.TypeIITrace
