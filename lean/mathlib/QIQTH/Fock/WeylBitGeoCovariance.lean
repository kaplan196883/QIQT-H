/-
  Increment 1 (per GPT-5.5-pro) — the abstract GEOMETRIC covariance interface for the Weyl-bit
  typicality measure.

  The prize theorem `weylBit_typicality_boost_invariant` says: boosting the one-particle modes `uᵢ ↦ A uᵢ`
  by an isometry `A` leaves the typicality measure μ∞ unchanged.  This module repackages that as an
  abstract LOCAL-NET covariance datum: a symmetry `π` RELABELING the mode index (e.g. a Poincaré element
  permuting spacetime regions), implemented on the one-particle space by an isometry `A`, with the modes
  EQUIVARIANT (`u (π i) = A (u i)`) and pairwise isotropic/microcausal (`Im⟪uᵢ,uⱼ⟫ = 0`).

  The conclusion (`GeoCovariantModes.typicality_invariant`) is that the σ-additive typicality measure for
  the geometrically-relabeled mode family `u ∘ π` equals the one for `u` — the measure does not depend on
  the frame/labeling chosen for the (commuting) modes.  This isolates the exact analytic obligations a
  concrete spacetime localization map `K : TestFun → H` would have to supply (`K_equivariance`,
  `microcausality`), so the entire probability/Fock argument downstream is reusable.  Axiom-free.
-/
import QIQTH.Fock.WeylBitMeasure
import Mathlib.Tactic

set_option linter.unusedSectionVars false

namespace QIQTH.Fock

open scoped InnerProductSpace
open MeasureTheory QIQTH.StateNetMeasure

variable {ι : Type*} [DecidableEq ι] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **The Born weight depends only on the mode FUNCTION**, not on the isotropy proof (which is a `Prop`):
    equal mode families give equal Born weights. -/
theorem bornWeight_mode_congr {u₁ u₂ : ι → H} (h : u₁ = u₂)
    (hiso₁ : ∀ i j, i ≠ j → Complex.im ⟪u₁ i, u₁ j⟫_ℂ = 0)
    (hiso₂ : ∀ i j, i ≠ j → Complex.im ⟪u₂ i, u₂ j⟫_ℂ = 0)
    (J : Finset ι) (σ : ∀ j : J, Bool) :
    bornWeight u₁ hiso₁ J σ = bornWeight u₂ hiso₂ J σ := by
  subst h; rfl

/-- **An abstract geometric-covariance datum** for the Weyl-bit net: a relabeling `π` of the mode index by
    a symmetry, implemented on the one-particle space by an isometry `A`, with the modes EQUIVARIANT and
    pairwise isotropic (microcausal). -/
structure GeoCovariantModes (ι : Type*) (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- the one-particle modes indexed by `ι`. -/
  u : ι → H
  /-- a symmetry relabeling the mode index (e.g. a Poincaré transformation of regions). -/
  π : ι ≃ ι
  /-- the one-particle implementation of the symmetry (e.g. the boost `U₁(t)`). -/
  A : H →ₗᵢ[ℂ] H
  /-- **equivariance**: relabeling a mode = applying the one-particle symmetry. -/
  equivariant : ∀ i, u (π i) = A (u i)
  /-- **microcausality / isotropy**: distinct modes are symplectically orthogonal. -/
  hiso : ∀ i j, i ≠ j → Complex.im ⟪u i, u j⟫_ℂ = 0

namespace GeoCovariantModes

variable (M : GeoCovariantModes ι H)

/-- The relabeled family `u ∘ π` is again pairwise isotropic (`π` is injective). -/
theorem hiso_relabel :
    ∀ i j, i ≠ j → Complex.im ⟪M.u (M.π i), M.u (M.π j)⟫_ℂ = 0 :=
  fun i j hij => M.hiso (M.π i) (M.π j) (fun h => hij (M.π.injective h))

/-- The relabeled family `u ∘ π` is the boosted family `A ∘ u` (equivariance). -/
theorem relabel_eq_boost : (fun i => M.u (M.π i)) = (fun i => M.A (M.u i)) :=
  funext M.equivariant

/-- **Geometric covariance of every Born weight**: the Born weight of the relabeled modes `u ∘ π` equals
    that of `u`.  (Relabeling = boosting, then `Γ(A)` is an isometry.) -/
theorem bornWeight_relabel (J : Finset ι) (σ : ∀ j : J, Bool) :
    bornWeight (fun i => M.u (M.π i)) M.hiso_relabel J σ = bornWeight M.u M.hiso J σ := by
  have hiso' : ∀ i j, i ≠ j → Complex.im ⟪M.A (M.u i), M.A (M.u j)⟫_ℂ = 0 :=
    fun i j hij => by rw [M.A.inner_map_map]; exact M.hiso i j hij
  rw [bornWeight_mode_congr M.relabel_eq_boost M.hiso_relabel hiso']
  exact bornWeight_isometry_invariant M.A M.u M.hiso hiso' J σ

/-- The relabeled and original Weyl-bit nets have the SAME finite Born marginals. -/
theorem marginals_invariant :
    (weylBitNet (fun i => M.u (M.π i)) M.hiso_relabel).toFiniteMarginals.μ
      = (weylBitNet M.u M.hiso).toFiniteMarginals.μ := by
  have hborn : ∀ (J : Finset ι) (x : ∀ j : J, Bool),
      (weylBitNet (fun i => M.u (M.π i)) M.hiso_relabel).bornPMF J x
        = (weylBitNet M.u M.hiso).bornPMF J x := by
    intro J x
    simp only [weylBitNet, EffectStateNet.bornPMF_apply, AddMonoidHom.id_apply, M.bornWeight_relabel]
  funext J
  exact congrArg PMF.toMeasure (PMF.ext (hborn J))

/-- **THE GEOMETRIC COVARIANCE OF μ∞:** the σ-additive Weyl-bit typicality measure for the
    geometrically-relabeled mode family `u ∘ π` equals the one for `u`.  So the typicality measure on the
    continuum free field is invariant under a symmetry of the (commuting) mode family implemented by a
    one-particle isometry — the abstract local-net covariance.  Specializing `π`/`A` to the Lorentz boost
    `U₁(t)` recovers frame-independence; a concrete spacetime localization `K` would supply `π`, `A`,
    `equivariant`, `hiso` from Poincaré covariance + Pauli–Jordan microcausality. -/
theorem typicality_invariant {μ ν : Measure (∀ _ : ι, Bool)}
    (hμ : (weylBitNet M.u M.hiso).toFiniteMarginals.IsLimit μ)
    (hν : (weylBitNet (fun i => M.u (M.π i)) M.hiso_relabel).toFiniteMarginals.IsLimit ν) :
    μ = ν := by
  refine (weylBitNet M.u M.hiso).toFiniteMarginals.limit_unique hμ ?_
  show MeasureTheory.IsProjectiveLimit ν ((weylBitNet M.u M.hiso).toFiniteMarginals.μ)
  rw [← M.marginals_invariant]
  exact hν

end GeoCovariantModes

end QIQTH.Fock
