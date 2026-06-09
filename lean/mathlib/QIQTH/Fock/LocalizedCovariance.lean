/-
  Boost-covariance of the LOCALIZED typicality measure — the reformulation that resolves the
  orbit/spacelike tension (§6b).

  The `SpacetimeLocalization` interface (LocalizationSkeleton.lean) requires a region family that is BOTH
  pairwise spacelike (`distinct_spacelike`, for microcausality) AND closed under a single boost relabel
  (`region_equivariant`).  These are GEOMETRICALLY INCOMPATIBLE for a non-vacuous family: a single boost
  ORBIT is pairwise TIMELIKE (`Δη² = 2r²(1−cosh Δθ) < 0`), so no boost-relabel-closed family is pairwise
  spacelike.

  The resolution: boost-covariance of the *measure* does NOT require the family to be closed under the boost.
  The Weyl-bit typicality measure depends only on the Gram matrix `⟪uᵢ,uⱼ⟫`, which any isometry preserves
  (`weylBit_typicality_boost_invariant`).  So we take a *pairwise-spacelike* (NOT boost-closed) region family
  — which exists freely (e.g. spatially separated bumps) — and the boost-covariance is exactly the
  isometry-invariance of the measure under `U₁(a) = boostUnitary a`, with the boosted family being the
  localization of the boosted regions (`K_boost_equivariant`).  No orbit, no tension.  Axiom-free.
-/
import QIQTH.Fock.PauliJordan
import QIQTH.Fock.WeylBitMeasure

set_option linter.unusedSectionVars false

namespace QIQTH.Fock.Localization

open scoped InnerProductSpace
open MeasureTheory

variable {ι : Type*} [DecidableEq ι]

/-- **Microcausality of a pairwise-spacelike localized family.**  For a family of localizable tests
`region : ι → LocalTest m` that are real, continuous, compactly supported, and *pairwise spacelike
separated* (NOT necessarily boost-closed), the localized modes `K(region i)` are pairwise symplectically
orthogonal — the `hiso` input the Weyl-bit measure needs.  Discharged from the proven microcausality
`K_im_inner_eq_zero_of_spacelike`. -/
theorem localized_hiso_of_spacelike (m : ℝ) (hm : m ≠ 0) (region : ι → LocalTest m)
    (hcont : ∀ i, Continuous (region i).f) (hcs : ∀ i, HasCompactSupport (region i).f)
    (hreal : ∀ i x, (starRingEnd ℂ) ((region i).f x) = (region i).f x)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ tsupport (region i).f, ∀ y ∈ tsupport (region j).f,
      Spacelike (x - y))
    (hKint : ∀ i j, Integrable
      (fun θ => (starRingEnd ℂ) (Krep m (region i).f θ) * Krep m (region j).f θ)) :
    ∀ i j, i ≠ j → Complex.im ⟪K m (region i), K m (region j)⟫_ℂ = 0 :=
  fun i j hij => K_im_inner_eq_zero_of_spacelike m hm (region i) (region j)
    (hcont i) (hcs i) (hcont j) (hcs j) (hreal i) (hreal j) (hsep i j hij) (hKint i j)

/-- The boosted localized family IS the localization of the boosted regions (`K_boost_equivariant`):
`U₁(a)(K(region i)) = K(boost_a · region i)`. -/
theorem boosted_localized_modes_eq (m a : ℝ) (region : ι → LocalTest m) :
    (fun i => boostUnitary a (K m (region i)))
      = (fun i => K m (boostLocalTest m a (region i))) :=
  funext fun i => (K_boost_equivariant m a (region i)).symm

/-- **★★ Boost-covariance of the localized typicality measure — the orbit/spacelike tension RESOLVED.**
For a *pairwise-spacelike* localized family `{K(region i)}` (microcausality `hiso`, NOT boost-closed), the
σ-additive Weyl-bit typicality measure μ∞ is the same as for the *boosted* family
`{U₁(a)(K(region i))} = {K(boost_a · region i)}`.  So the typicality measure on the local relativistic
field records is Lorentz-boost invariant — *without* requiring the regions to be closed under the boost.
The boost-covariance is the isometry-invariance of the measure (`weylBit_typicality_boost_invariant`); the
boosted family is the localization of the boosted regions (`boosted_localized_modes_eq`).  Axiom-free. -/
theorem localized_typicality_boost_invariant (m a : ℝ) (region : ι → LocalTest m)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪K m (region i), K m (region j)⟫_ℂ = 0)
    {μ ν : Measure (∀ _ : ι, Bool)}
    (hμ : (weylBitNet (fun i => K m (region i)) hiso).toFiniteMarginals.IsLimit μ)
    (hν : (weylBitNet (fun i => boostUnitary a (K m (region i)))
            (fun i j hij => by
              rw [LinearIsometry.inner_map_map]; exact hiso i j hij)).toFiniteMarginals.IsLimit ν) :
    μ = ν :=
  weylBit_typicality_boost_invariant (boostUnitary a) (fun i => K m (region i)) hiso
    (fun i j hij => by rw [LinearIsometry.inner_map_map]; exact hiso i j hij) hμ hν

end QIQTH.Fock.Localization
