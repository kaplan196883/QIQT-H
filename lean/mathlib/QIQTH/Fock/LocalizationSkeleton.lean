/-
  Stage 2 SKELETON — the spacetime-localization interface for the Weyl-bit typicality measure.

  The measure-level prize (`WeylBitMeasure.lean`, `WeylBitGeoCovariance.lean`) builds, axiom-free, a
  σ-additive boost-covariant, pushforward-invariant typicality measure μ∞ over the histories of an
  ABSTRACT pairwise-isotropic ("microcausal") family of one-particle modes `u : ι → H` with a symmetry
  `π` relabeling the index, implemented by a one-particle isometry `A`.

  What makes that family GENUINELY a *spacetime-local relativistic field* — rather than an abstract abelian
  Weyl-bit process — is a **localization map** `K : TestFun → H` from spacetime test functions to the
  one-particle space, with two physical properties:

    * **Poincaré equivariance** `K(boost · f) = U₁(t)(K f)` — the localization intertwines the spacetime
      Poincaré action with the one-particle representation;
    * **Pauli–Jordan microcausality** `Im⟪K f, K g⟫ = 0` whenever `f`, `g` are supported in mutually
      *spacelike* regions — Einstein causality / no-signaling between spacelike-separated observables.

  This module packages exactly those obligations as the `SpacetimeLocalization` interface and proves that
  ANY such datum yields a `GeoCovariantModes` datum, hence the existence + boost-covariance +
  single-measure pushforward-invariance of μ∞ over the LOCAL field records.  The Pauli–Jordan vanishing and
  the equivariance are CITED inputs (hypothesis fields) — constructing a concrete `K` from the Fourier /
  mass-shell transform and the Minkowski spacelike geometry is the genuine multi-month physics program
  (the "real wall"); this skeleton isolates precisely what that construction must supply so that the entire
  probability/Fock argument downstream is reused unchanged.  Axiom-free.
-/
import QIQTH.Fock.WeylBitGeoCovariance
import Mathlib.Tactic

set_option linter.unusedSectionVars false

namespace QIQTH.Fock

open scoped InnerProductSpace
open MeasureTheory QIQTH.StateNetMeasure

variable {ι : Type*} [DecidableEq ι] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {TestFun : Type*}

/-- **The spacetime-localization interface (Stage 2 skeleton).**  A localization map `K` from spacetime
    test functions to the one-particle space, a family of test functions `region i` localized in the
    spacetime regions indexed by `ι`, a spacetime boost `boostT` on test functions implemented on the
    one-particle space by the isometry `A` (e.g. `U₁(t)`), the induced relabeling `relabel` of regions, and
    the two physical inputs: **Poincaré equivariance** (`K_equivariant` + `region_equivariant`) and
    **Pauli–Jordan microcausality** (`pauli_jordan`: spacelike test functions are symplectically
    orthogonal).  `K` is concretely an ℝ-linear map; only the equivariance and microcausality of the
    localized modes are consumed downstream, so it is left as a bare function here. -/
structure SpacetimeLocalization (ι : Type*) (H : Type*) (TestFun : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- the localization map from spacetime test functions to the one-particle space. -/
  K : TestFun → H
  /-- the test function localized in spacetime region `i`. -/
  region : ι → TestFun
  /-- the spacetime boost acting on test functions. -/
  boostT : TestFun → TestFun
  /-- the relabeling of regions induced by the boost. -/
  relabel : ι ≃ ι
  /-- the one-particle implementation of the boost (e.g. `U₁(t)`). -/
  A : H →ₗᵢ[ℂ] H
  /-- **Poincaré equivariance of the localization map**: `K(boost · f) = A(K f)`. -/
  K_equivariant : ∀ f, K (boostT f) = A (K f)
  /-- **equivariance of the region family**: boosting a region relabels it. -/
  region_equivariant : ∀ i, region (relabel i) = boostT (region i)
  /-- the spacelike-separation relation between region indices. -/
  spacelike : ι → ι → Prop
  /-- the chosen record regions are pairwise spacelike (a single decoherent, jointly measurable family —
      the Fine/Bell-safe hypothesis: records, not counterfactual incompatible settings). -/
  distinct_spacelike : ∀ i j, i ≠ j → spacelike i j
  /-- **Pauli–Jordan microcausality** (CITED physics input): spacelike-separated localized observables are
      symplectically orthogonal, `Im⟪K f, K g⟫ = 0`. -/
  pauli_jordan : ∀ i j, spacelike i j → Complex.im ⟪K (region i), K (region j)⟫_ℂ = 0

namespace SpacetimeLocalization

variable (L : SpacetimeLocalization ι H TestFun)

/-- The one-particle modes obtained by localizing the region test functions: `uᵢ = K(region i)`. -/
def modes : ι → H := fun i => L.K (L.region i)

/-- The localized modes are pairwise isotropic (microcausal): distinct regions are spacelike
    (`distinct_spacelike`), hence symplectically orthogonal (`pauli_jordan`). -/
theorem modes_hiso : ∀ i j, i ≠ j → Complex.im ⟪L.modes i, L.modes j⟫_ℂ = 0 :=
  fun i j hij => L.pauli_jordan i j (L.distinct_spacelike i j hij)

/-- The localized modes are equivariant: relabeling a region = applying the one-particle boost
    (`region_equivariant` then `K_equivariant`). -/
theorem modes_equivariant : ∀ i, L.modes (L.relabel i) = L.A (L.modes i) := by
  intro i
  show L.K (L.region (L.relabel i)) = L.A (L.K (L.region i))
  rw [L.region_equivariant, L.K_equivariant]

/-- **A spacetime localization produces a geometric-covariance datum.**  The localized, microcausal,
    equivariant mode family is exactly a `GeoCovariantModes` — so the entire boost-covariance /
    pushforward machinery applies to the LOCAL field records. -/
def toGeoCovariantModes : GeoCovariantModes ι H where
  u := L.modes
  π := L.relabel
  A := L.A
  equivariant := L.modes_equivariant
  hiso := L.modes_hiso

/-- **The localized free-field typicality measure exists.**  Over the records of the spacelike-local family
    `{K(region i)}`, the σ-additive Weyl-bit Born typicality measure μ∞ exists (and is a genuine,
    non-deterministic probability distribution determined by the quasifree vacuum two-point function). -/
theorem localized_typicality_exists :
    ∃ μ : Measure (∀ _ : ι, Bool), IsProbabilityMeasure μ ∧
      (weylBitNet L.modes L.modes_hiso).toFiniteMarginals.IsLimit μ :=
  weylBit_typicalityMeasure_exists L.modes L.modes_hiso

/-- **Boost-covariance of the localized typicality measure (per-frame form).**  The measure realizing the
    records of the boosted region family `region ∘ relabel` equals the one for `region`: the local-field
    typicality measure does not depend on the Lorentz frame. -/
theorem localized_typicality_invariant {μ ν : Measure (∀ _ : ι, Bool)}
    (hμ : (weylBitNet L.modes L.modes_hiso).toFiniteMarginals.IsLimit μ)
    (hν : (weylBitNet (fun i => L.modes (L.relabel i)) L.toGeoCovariantModes.hiso_relabel
            ).toFiniteMarginals.IsLimit ν) :
    μ = ν :=
  L.toGeoCovariantModes.typicality_invariant hμ hν

/-- **THE LOCALIZED PRIZE (skeleton): the single-measure pushforward covariance of the local-field μ∞.**
    Given a spacetime localization with Pauli–Jordan microcausality and Poincaré equivariance, the
    σ-additive typicality measure μ∞ over the spacelike-local field records is FIXED, as a single measure,
    by the spacetime symmetry `π = relabel` acting on the history space: `(historyAct π)_* μ∞ = μ∞`.

    Modulo the cited construction of a concrete `K` (the multi-month Pauli–Jordan / Wightman program), this
    is the literal Open-Problem-3b statement on the relativistic free field: a canonical, Lorentz-covariant
    typicality measure over the local record histories.  Axiom-free. -/
theorem localized_typicality_pushforward_invariant {μ : Measure (∀ _ : ι, Bool)}
    (hμ : (weylBitNet L.modes L.modes_hiso).toFiniteMarginals.IsLimit μ) :
    μ.map L.toGeoCovariantModes.historyAct = μ :=
  L.toGeoCovariantModes.typicality_pushforward_invariant hμ

end SpacetimeLocalization

/-- **Non-vacuity witness**: the localization interface is inhabited, so its hypotheses are jointly
    satisfiable (no soundness/vacuity hole).  This witness is DEGENERATE — constant zero modes, identity
    boost, all regions declared spacelike — and is included only to certify the interface is consistent; a
    NON-trivial instance, with genuine spacelike-separated regions and a real Poincaré action implemented by
    `U₁(t)`, is exactly the cited concrete-`K` construction (the multi-month Pauli–Jordan / Wightman
    program), not a formalizable gap. -/
def trivialLocalization (ι : Type*) (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
    SpacetimeLocalization ι H H where
  K := id
  region := fun _ => 0
  boostT := id
  relabel := Equiv.refl ι
  A := LinearIsometry.id
  K_equivariant := fun f => by simp
  region_equivariant := fun _ => rfl
  spacelike := fun _ _ => True
  distinct_spacelike := fun _ _ _ => trivial
  pauli_jordan := fun _ _ _ => by simp

end QIQTH.Fock
