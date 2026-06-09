/-
  A CONCRETE non-degenerate boost-orbit instance of the geometric-covariance datum (per GPT-5.5-pro's
  "minimal pushforward-invariant K milestone").

  The abstract `GeoCovariantModes`/`typicality_pushforward_invariant` results give a boost-covariant,
  single-measure-pushforward-invariant typicality measure μ∞ for ANY equivariant microcausal mode family.
  The `trivialLocalization` witness inhabits that interface only degenerately (zero modes, identity boost).
  Here we build a GENUINELY non-degenerate instance: the discrete boost orbit on the continuum one-particle
  space `L²(ℝ)`.

  Fix a rapidity `τ` and a seed `u₀`.  Index the records by `ℤ`, with the n-th mode the `nτ`-boost of the
  seed, `uₙ = U₁(nτ) u₀`.  The Lorentz boost of rapidity `τ` then acts on the orbit by the **shift**
  `n ↦ n+1` (`U₁(τ) uₙ = u_{n+1}`), the exact `n ↦ n+1` geometry of an infinite spacelike family of
  boost-translates (the lattice on a proper-time hyperbola).  Equivariance and the reduction of microcausality
  to the SINGLE seed condition `Im⟪u₀, U₁(kτ)u₀⟫ = 0  (k ≠ 0)` are PROVEN here from the `boostUnitary` group
  law; that seed condition is the residual Pauli–Jordan input (it holds for genuinely spacelike-separated
  localizations — the cited analytic frontier — and is left as the single hypothesis).

  Consequence: the σ-additive Weyl-bit typicality measure μ∞ over the boost orbit exists and is FIXED, as a
  single measure, by the boost-induced shift `n ↦ n+1` on the history space `∏_{n:ℤ} {±1}`
  (`boostOrbit_typicality_pushforward_invariant`).  Axiom-free; the only physical hypothesis is the seed
  symplectic-orthogonality `hiso0`.
-/
import QIQTH.Fock.WeylBitGeoCovariance
import QIQTH.Fock.OneParticle
import Mathlib.Tactic

set_option linter.unusedSectionVars false

namespace QIQTH.Fock

open scoped InnerProductSpace
open MeasureTheory

/-- The 1+1D one-particle space `L²(ℝ)` (rapidity coordinate). -/
abbrev OneP : Type := Lp ℂ 2 (volume : Measure ℝ)

/-- **The discrete boost orbit as a geometric-covariance datum.**  Modes `uₙ = U₁(nτ) u₀` indexed by `ℤ`,
    with the boost of rapidity `τ` acting by the shift `n ↦ n+1` (implemented by `U₁(τ)`).  Equivariance is
    proven from the group law; microcausality is reduced to the seed condition `hiso0`. -/
noncomputable def boostOrbitModes (τ : ℝ) (u0 : OneP)
    (hiso0 : ∀ k : ℤ, k ≠ 0 → Complex.im ⟪u0, OneParticle.boostUnitary ((k : ℝ) * τ) u0⟫_ℂ = 0) :
    GeoCovariantModes ℤ OneP where
  u := fun n => OneParticle.boostUnitary ((n : ℝ) * τ) u0
  π := Equiv.addRight (1 : ℤ)
  A := (OneParticle.boostUnitary τ).toLinearIsometry
  equivariant := by
    intro n
    show OneParticle.boostUnitary (((n + 1 : ℤ) : ℝ) * τ) u0
      = (OneParticle.boostUnitary τ).toLinearIsometry (OneParticle.boostUnitary ((n : ℝ) * τ) u0)
    simp only [LinearIsometryEquiv.coe_toLinearIsometry]
    rw [← OneParticle.boostUnitary_add_apply]
    congr 1
    push_cast; ring
  hiso := by
    intro n m hnm
    have hsplit : OneParticle.boostUnitary ((m : ℝ) * τ) u0
        = OneParticle.boostUnitary ((n : ℝ) * τ)
            (OneParticle.boostUnitary (((m - n : ℤ) : ℝ) * τ) u0) := by
      rw [← OneParticle.boostUnitary_add_apply]
      congr 1
      push_cast; ring
    have key : (⟪OneParticle.boostUnitary ((n : ℝ) * τ) u0,
        OneParticle.boostUnitary ((m : ℝ) * τ) u0⟫_ℂ : ℂ)
        = ⟪u0, OneParticle.boostUnitary (((m - n : ℤ) : ℝ) * τ) u0⟫_ℂ := by
      rw [hsplit, LinearIsometryEquiv.inner_map_map]
    show Complex.im (⟪OneParticle.boostUnitary ((n : ℝ) * τ) u0,
      OneParticle.boostUnitary ((m : ℝ) * τ) u0⟫_ℂ) = 0
    rw [key]
    exact hiso0 (m - n) (sub_ne_zero.mpr (Ne.symm hnm))

/-- **The σ-additive Weyl-bit typicality measure over the boost orbit exists.** -/
theorem boostOrbit_typicality_exists (τ : ℝ) (u0 : OneP)
    (hiso0 : ∀ k : ℤ, k ≠ 0 → Complex.im ⟪u0, OneParticle.boostUnitary ((k : ℝ) * τ) u0⟫_ℂ = 0) :
    ∃ μ : Measure (∀ _ : ℤ, Bool), IsProbabilityMeasure μ ∧
      (weylBitNet (boostOrbitModes τ u0 hiso0).u (boostOrbitModes τ u0 hiso0).hiso
        ).toFiniteMarginals.IsLimit μ :=
  weylBit_typicalityMeasure_exists _ _

/-- **THE BOOST-ORBIT PUSHFORWARD COVARIANCE.**  The typicality measure μ∞ over the discrete boost orbit on
    `L²(ℝ)` is FIXED, as a single measure, by the Lorentz-boost-induced shift `n ↦ n+1` acting on the history
    space `∏_{n:ℤ} {±1}`: `(historyAct (· + 1))_* μ∞ = μ∞`.  This is a genuinely non-degenerate (continuum,
    real-boost-orbit) realization of the geometric pushforward covariance — modulo only the seed
    symplectic-orthogonality `hiso0` (the residual Pauli–Jordan input).  Axiom-free. -/
theorem boostOrbit_typicality_pushforward_invariant (τ : ℝ) (u0 : OneP)
    (hiso0 : ∀ k : ℤ, k ≠ 0 → Complex.im ⟪u0, OneParticle.boostUnitary ((k : ℝ) * τ) u0⟫_ℂ = 0)
    {μ : Measure (∀ _ : ℤ, Bool)}
    (hμ : (weylBitNet (boostOrbitModes τ u0 hiso0).u (boostOrbitModes τ u0 hiso0).hiso
            ).toFiniteMarginals.IsLimit μ) :
    μ.map (boostOrbitModes τ u0 hiso0).historyAct = μ :=
  (boostOrbitModes τ u0 hiso0).typicality_pushforward_invariant hμ

end QIQTH.Fock
