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

/-! ### Reindexing the Born law by an index bijection (the `noncommProd` reindex Mathlib lacks)

These lemmas reindex the order-independent Born history vector / Born weight along a bijection `π` of the
mode index, proved by induction on the context (no `Multiset` gymnastics) — the missing ingredient for the
LITERAL single-measure pushforward `(historyAct π)_* μ∞ = μ∞`. -/

/-- **Reindex the Born history vector by an index bijection** `π`: the order-independent product over
    `J.map π` of the bits of `v` equals the product over `J` of the bits of the relabeled family `v ∘ π`. -/
theorem bornVecTot_map (v : ι → H) (π : ι ≃ ι)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪v i, v j⟫_ℂ = 0)
    (hiso' : ∀ i j, i ≠ j → Complex.im ⟪v (π i), v (π j)⟫_ℂ = 0)
    (s : ι → ℂ) (J : Finset ι) :
    bornVecTot v hiso s (J.map π.toEmbedding)
      = bornVecTot (fun i => v (π i)) hiso' (fun i => s (π i)) J := by
  classical
  induction J using Finset.induction with
  | empty => simp [bornVecTot_empty]
  | @insert a J' ha ih =>
    have hπa : π.toEmbedding a ∉ J'.map π.toEmbedding := by rw [Finset.mem_map']; exact ha
    rw [Finset.map_insert, bornVecTot_insert v hiso s hπa,
      bornVecTot_insert (fun i => v (π i)) hiso' (fun i => s (π i)) ha, ih]
    simp only [Equiv.coe_toEmbedding]

/-- Reindex a `J`-outcome to a `J.map π`-outcome along the bijection `k = π j`. -/
def outReindex (π : ι ≃ ι) (J : Finset ι) (σ : ∀ j : J, Bool) :
    ∀ k : (J.map π.toEmbedding : Finset ι), Bool :=
  fun k => σ ⟨π.symm k, Finset.mem_map_equiv.mp k.2⟩

/-- **Reindex the Born weight by an index bijection** `π`: the Born weight of the reindexed outcome on the
    relabeled context `J.map π` equals the Born weight of the original outcome for the relabeled family. -/
theorem bornWeight_map (v : ι → H) (π : ι ≃ ι)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪v i, v j⟫_ℂ = 0)
    (hiso' : ∀ i j, i ≠ j → Complex.im ⟪v (π i), v (π j)⟫_ℂ = 0)
    (J : Finset ι) (σ : ∀ j : J, Bool) :
    bornWeight v hiso (J.map π.toEmbedding) (outReindex π J σ)
      = bornWeight (fun i => v (π i)) hiso' J σ := by
  rw [bornWeight, bornWeight, bornVecTot_map v π hiso hiso']
  have hsig : bornVecTot (fun i => v (π i)) hiso'
        (fun i => signExt (J.map π.toEmbedding) (outReindex π J σ) (π i)) J
      = bornVecTot (fun i => v (π i)) hiso' (signExt J σ) J := by
    refine bornVecTot_congr (fun i => v (π i)) hiso' (fun i hi => ?_)
    have hπi : π i ∈ J.map π.toEmbedding := by
      rw [show π i = π.toEmbedding i from rfl, Finset.mem_map']; exact hi
    rw [signExt, dif_pos hπi, signExt, dif_pos hi]
    have hsub : (⟨π.symm (π i), Finset.mem_map_equiv.mp hπi⟩ : J) = ⟨i, hi⟩ :=
      Subtype.ext (π.symm_apply_apply i)
    simp only [outReindex, hsub]
  rw [hsig]

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

/-! ### The literal single-measure pushforward `(historyAct π)_* μ∞ = μ∞` -/

/-- **Born weight is invariant under the `π`-reindex of contexts** for the equivariant family: combine the
    pure index reindex (`bornWeight_map`) with the equivariance/isometry relabel (`bornWeight_relabel`). -/
theorem bornWeight_map_invariant (J : Finset ι) (σ : ∀ j : J, Bool) :
    bornWeight M.u M.hiso (J.map M.π.toEmbedding) (outReindex M.π J σ)
      = bornWeight M.u M.hiso J σ := by
  rw [bornWeight_map M.u M.π M.hiso M.hiso_relabel, M.bornWeight_relabel]

/-- The action of the symmetry `π` on the Weyl-bit history space `∀ i, Bool`, `g ↦ g ∘ π`. -/
def historyAct : (∀ _ : ι, Bool) → (∀ _ : ι, Bool) := fun g i => g (M.π i)

/-- The history-space action of `π` is measurable (it is a coordinate relabeling). -/
theorem measurable_historyAct : Measurable M.historyAct :=
  measurable_pi_lambda _ (fun i => measurable_pi_apply (M.π i))

/-- **THE LITERAL PUSHFORWARD COVARIANCE OF μ∞.**  The σ-additive Weyl-bit typicality measure μ∞ is
    invariant *as a single measure* under the action of the symmetry `π` on the history space:
    `(historyAct π)_* μ∞ = μ∞`.  This strengthens `typicality_invariant` (which equated the two measures
    realizing the `u` and `u ∘ π` families) to the textbook covariance statement — the one measure μ∞ is
    fixed by the symmetry.  Proof: the pushforward's `J`-marginal is the `μ`-marginal on the relabeled
    context `J.map π` reindexed back (singleton-level set identity), and the Born weights are π-invariant
    (`bornWeight_map_invariant`), so the pushforward realizes the SAME projective family; uniqueness of the
    Kolmogorov limit (`isLimit_map_eq`) gives equality.  Axiom-free. -/
theorem typicality_pushforward_invariant {μ : Measure (∀ _ : ι, Bool)}
    (hμ : (weylBitNet M.u M.hiso).toFiniteMarginals.IsLimit μ) :
    μ.map M.historyAct = μ := by
  refine HistoryMeasure.isLimit_map_eq hμ (fun J => ?_)
  rw [Measure.map_map (Finset.measurable_restrict J) M.measurable_historyAct]
  refine Measure.ext_of_singleton (fun σ => ?_)
  have hset : (J.restrict ∘ M.historyAct) ⁻¹' {σ}
      = (Finset.restrict (π := fun _ : ι => Bool) (J.map M.π.toEmbedding)) ⁻¹'
          {outReindex M.π J σ} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply]
    constructor
    · intro h
      funext k
      have hk : M.π.symm ↑k ∈ J := Finset.mem_map_equiv.mp k.2
      have hc := congrFun h ⟨M.π.symm ↑k, hk⟩
      simp only [Finset.restrict, historyAct, Equiv.apply_symm_apply] at hc
      simp only [Finset.restrict, outReindex]
      exact hc
    · intro h
      funext j
      have hπj : M.π ↑j ∈ J.map M.π.toEmbedding := by
        rw [show M.π ↑j = M.π.toEmbedding ↑j from rfl, Finset.mem_map']; exact j.2
      have hc := congrFun h ⟨M.π ↑j, hπj⟩
      simp only [Finset.restrict, outReindex, Equiv.symm_apply_apply] at hc
      simp only [Finset.restrict, historyAct]
      rw [hc, Subtype.coe_eta]
  rw [Measure.map_apply ((Finset.measurable_restrict J).comp M.measurable_historyAct)
        (measurableSet_singleton σ), hset,
      ← Measure.map_apply (Finset.measurable_restrict _) (measurableSet_singleton _),
      hμ (J.map M.π.toEmbedding)]
  show ((weylBitNet M.u M.hiso).bornPMF (J.map M.π.toEmbedding)).toMeasure {outReindex M.π J σ}
      = ((weylBitNet M.u M.hiso).bornPMF J).toMeasure {σ}
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      EffectStateNet.bornPMF_apply, EffectStateNet.bornPMF_apply]
  simp only [weylBitNet, AddMonoidHom.id_apply]
  rw [bornWeight_map_invariant]

end GeoCovariantModes

end QIQTH.Fock
