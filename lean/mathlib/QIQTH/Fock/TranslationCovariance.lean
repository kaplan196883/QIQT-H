/-
  Translation-covariance of the LOCALIZED typicality measure — the second generator of the connected
  Poincaré group (§6c), completing boost-covariance (`LocalizedCovariance.lean`) to FULL connected
  Poincaré covariance.

  The boost acts on the localized rapidity amplitudes as the measure-preserving translation `θ ↦ θ + a`
  (a *composition* isometry, `boostUnitary`).  A spacetime translation `τ_b` acts DIFFERENTLY: by
  `Krep_translate`, it multiplies the amplitude pointwise by the unit-modulus phase
  `e^{−i η(p_m θ, b)}` — a `θ`-dependent unimodular multiplier, NOT a translation.  But a `θ`-dependent
  unit-modulus multiplier is still a unitary MULTIPLICATION operator on `L²(ℝ, dθ)`: it preserves every
  inner product, because `|e^{−i η(p_m θ, b)}| = 1` pointwise cancels in `⟪M_b u, M_b v⟫ = ∫ \overline{φ}φ
  \bar u v = ∫ \bar u v = ⟪u, v⟫`.  So the SAME Gram-matrix argument that gave boost-covariance gives
  translation-covariance, and boosts + translations generate the connected Poincaré group.  Axiom-free.
-/
import QIQTH.Fock.PauliJordan
import QIQTH.Fock.WeylBitMeasure

set_option linter.unusedSectionVars false

namespace QIQTH.Fock.Localization

open scoped InnerProductSpace
open MeasureTheory

/-! ### The unimodular translation phase on the one-particle space -/

/-- **The translation phase multiplier** `φ_b(θ) = e^{−i η(p_m θ, b)}` — the unit-modulus function by which
a spacetime translation `τ_b` multiplies the localized rapidity amplitude (`Krep_translate`). -/
noncomputable def translationPhase (m : ℝ) (b : V) (θ : ℝ) : ℂ :=
  Complex.exp (-Complex.I * ((minkowskiDot (massShell m θ) b : ℝ) : ℂ))

/-- The translation phase has modulus one (`|e^{−i η}| = 1`). -/
theorem norm_translationPhase (m : ℝ) (b : V) (θ : ℝ) : ‖translationPhase m b θ‖ = 1 := by
  rw [translationPhase, show (-Complex.I * ((minkowskiDot (massShell m θ) b : ℝ) : ℂ))
      = ((-(minkowskiDot (massShell m θ) b) : ℝ) : ℂ) * Complex.I from by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

/-- The translation phase is continuous in `θ`. -/
theorem continuous_translationPhase (m : ℝ) (b : V) : Continuous (translationPhase m b) := by
  refine Complex.continuous_exp.comp (Continuous.mul continuous_const ?_)
  exact Complex.continuous_ofReal.comp ((continuous_minkowskiDot_fst b).comp (continuous_massShell m))

/-- The translation phase is essentially bounded (`L^∞`), being continuous of modulus one. -/
theorem memLp_top_translationPhase (m : ℝ) (b : V) :
    MemLp (translationPhase m b) ⊤ (volume : Measure ℝ) :=
  memLp_top_of_bound (continuous_translationPhase m b).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun θ => le_of_eq (norm_translationPhase m b θ))

/-! ### The multiplication operator `M_b` and its isometry property -/

/-- `φ_b · ψ ∈ L²` for `ψ ∈ L²` (`L^∞ · L² ⊆ L²`), with the exponent pinned to `2`. -/
theorem memLp_phase_mul (m : ℝ) (b : V) (ψ : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (fun θ => translationPhase m b θ * ψ θ) 2 (volume : Measure ℝ) :=
  (Lp.memLp ψ).mul' (memLp_top_translationPhase m b)

/-- **The translation multiplier `M_b` on `L²(ℝ)`** as a `ℂ`-linear map `ψ ↦ φ_b · ψ`.  Well-defined
(`memLp_phase_mul`: `L^∞ · L² ⊆ L²`), `ℂ`-linear by the pointwise algebra of multiplication. -/
noncomputable def multiplierMap (m : ℝ) (b : V) :
    Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun ψ := (memLp_phase_mul m b ψ).toLp _
  map_add' ψ φ := by
    apply Lp.ext
    filter_upwards [(memLp_phase_mul m b (ψ + φ)).coeFn_toLp,
      Lp.coeFn_add ((memLp_phase_mul m b ψ).toLp _) ((memLp_phase_mul m b φ).toLp _),
      (memLp_phase_mul m b ψ).coeFn_toLp, (memLp_phase_mul m b φ).coeFn_toLp,
      Lp.coeFn_add ψ φ] with θ h1 h2 h3 h4 h5
    simp only [Pi.add_apply, h1, h2, h3, h4, h5]
    ring
  map_smul' c ψ := by
    apply Lp.ext
    filter_upwards [(memLp_phase_mul m b (c • ψ)).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_phase_mul m b ψ).toLp _),
      (memLp_phase_mul m b ψ).coeFn_toLp, Lp.coeFn_smul c ψ] with θ h1 h2 h3 h4
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, h1, h2, h3, h4]
    ring

/-- The pointwise action of the multiplier: `⇑(M_b ψ) =ᵐ φ_b · ψ`. -/
theorem multiplierMap_coeFn (m : ℝ) (b : V) (ψ : Lp ℂ 2 (volume : Measure ℝ)) :
    ⇑(multiplierMap m b ψ) =ᵐ[volume] fun θ => translationPhase m b θ * ψ θ :=
  (memLp_phase_mul m b ψ).coeFn_toLp

/-- **`M_b` preserves the `L²` inner product** — the unit-modulus phase cancels:
`⟪M_b φ, M_b ψ⟫ = ∫ \overline{φ_b}φ_b · \overline{φ}ψ = ∫ \overline{φ}ψ = ⟪φ, ψ⟫`. -/
theorem multiplier_inner (m : ℝ) (b : V) (φ ψ : Lp ℂ 2 (volume : Measure ℝ)) :
    ⟪multiplierMap m b φ, multiplierMap m b ψ⟫_ℂ = ⟪φ, ψ⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [multiplierMap_coeFn m b φ, multiplierMap_coeFn m b ψ] with θ hφ hψ
  rw [hφ, hψ,
    show (translationPhase m b θ * φ θ) = translationPhase m b θ • (φ θ : ℂ) from (smul_eq_mul _ _).symm,
    show (translationPhase m b θ * ψ θ) = translationPhase m b θ • (ψ θ : ℂ) from (smul_eq_mul _ _).symm,
    inner_smul_left, inner_smul_right, ← mul_assoc,
    show (starRingEnd ℂ) (translationPhase m b θ) * translationPhase m b θ = 1 from by
      rw [RCLike.conj_mul]; simp [norm_translationPhase m b θ], one_mul]

/-- **The translation multiplier `M_b` as a one-particle isometry** `L²(ℝ) →ₗᵢ[ℂ] L²(ℝ)`.  Unitary because
the multiplier `φ_b` has modulus one (`multiplier_inner`).  This is the translation counterpart of the
rapidity-translation isometry `boostUnitary`. -/
noncomputable def multiplierIsometry (m : ℝ) (b : V) :
    Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (multiplierMap m b).isometryOfInner (multiplier_inner m b)

@[simp] theorem multiplierIsometry_apply (m : ℝ) (b : V) (ψ : Lp ℂ 2 (volume : Measure ℝ)) :
    multiplierIsometry m b ψ = multiplierMap m b ψ := rfl

/-! ### The translated localizable test and the equivariance `K(τ_b f) = M_b (K f)` -/

/-- The spacetime translation `τ_b` acting on a localizable test — the amplitude stays in `L²` because the
multiplier `φ_b` is bounded (`L^∞ · L² ⊆ L²`). -/
noncomputable def translateLocalTest (m : ℝ) (b : V) (Lf : LocalTest m) : LocalTest m where
  f := translateTest b Lf.f
  memLp := by
    rw [show Krep m (translateTest b Lf.f) = fun θ => translationPhase m b θ * Krep m Lf.f θ from
      funext fun θ => Krep_translate m b Lf.f θ]
    exact Lf.memLp.mul' (memLp_top_translationPhase m b)

/-- **★ Translation equivariance of the localization map `K`.**  `K (τ_b f) = M_b (K f)`: a spacetime
translation by `b` is intertwined by `K` with the one-particle multiplier isometry `M_b` on `L²(ℝ)`.  This
is the second Poincaré generator (the first being the boost, `K_boost_equivariant`); together they give full
connected-Poincaré equivariance.  Immediate from the amplitude-level multiplier identity `Krep_translate`. -/
theorem K_translate_equivariant (m : ℝ) (b : V) (Lf : LocalTest m) :
    K m (translateLocalTest m b Lf) = multiplierIsometry m b (K m Lf) := by
  apply Lp.ext
  have e1 : (⇑(K m (translateLocalTest m b Lf)) : ℝ → ℂ) =ᵐ[volume]
      Krep m (translateTest b Lf.f) := (translateLocalTest m b Lf).memLp.coeFn_toLp
  have e3 : (⇑(K m Lf) : ℝ → ℂ) =ᵐ[volume] Krep m Lf.f := Lf.memLp.coeFn_toLp
  filter_upwards [e1, multiplierMap_coeFn m b (K m Lf), e3] with θ h1 h2 h3
  rw [multiplierIsometry_apply, h2, h1, Krep_translate, h3, translationPhase]

/-! ### Translation-covariance and full connected-Poincaré covariance of the typicality measure -/

variable {ι : Type*} [DecidableEq ι]

/-- The translated localized family IS the localization of the translated regions (`K_translate_equivariant`):
`M_b (K(region i)) = K(τ_b · region i)`. -/
theorem translated_localized_modes_eq (m : ℝ) (b : V) (region : ι → LocalTest m) :
    (fun i => multiplierIsometry m b (K m (region i)))
      = (fun i => K m (translateLocalTest m b (region i))) :=
  funext fun i => (K_translate_equivariant m b (region i)).symm

/-- **★★ Translation-covariance of the localized typicality measure.**  For a pairwise-spacelike localized
family `{K(region i)}` (microcausality `hiso`), the σ-additive Weyl-bit typicality measure μ∞ is the same as
for the *translated* family `{M_b(K(region i))} = {K(τ_b · region i)}`.  So the typicality measure is
invariant under spacetime translations — the second generator of the connected Poincaré group.  The
translation-covariance is the isometry-invariance of the measure (`weylBit_typicality_boost_invariant` with
the multiplier isometry `M_b`); the translated family is the localization of the translated regions
(`translated_localized_modes_eq`).  Axiom-free. -/
theorem localized_typicality_translation_invariant (m : ℝ) (b : V) (region : ι → LocalTest m)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪K m (region i), K m (region j)⟫_ℂ = 0)
    {μ ν : Measure (∀ _ : ι, Bool)}
    (hμ : (weylBitNet (fun i => K m (region i)) hiso).toFiniteMarginals.IsLimit μ)
    (hν : (weylBitNet (fun i => multiplierIsometry m b (K m (region i)))
            (fun i j hij => by
              rw [LinearIsometry.inner_map_map]; exact hiso i j hij)).toFiniteMarginals.IsLimit ν) :
    μ = ν :=
  weylBit_typicality_boost_invariant (multiplierIsometry m b) (fun i => K m (region i)) hiso
    (fun i j hij => by rw [LinearIsometry.inner_map_map]; exact hiso i j hij) hμ hν

/-- **The full connected-Poincaré isometry** `U(a,b) = M_b ∘ U₁(a)` on `L²(ℝ)`: rapidity boost `a` followed
by spacetime translation `b`.  The connected Poincaré group of 1+1D Minkowski space is generated by boosts
and translations, so this composite (with all `a, b`) realizes the whole connected group on the one-particle
space. -/
noncomputable def poincareIsometry (m a : ℝ) (b : V) :
    Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (multiplierIsometry m b).comp (boostUnitary a)

/-- **★★★ Full connected-Poincaré equivariance of `K`.**  `K (τ_b · β_a · f) = U(a,b) (K f)`: an arbitrary
connected-Poincaré transformation (boost `a` then translation `b`) of the spacetime test is intertwined by
`K` with the composite one-particle isometry `U(a,b) = M_b ∘ U₁(a)`.  Combines `K_boost_equivariant` and
`K_translate_equivariant`. -/
theorem K_poincare_equivariant (m a : ℝ) (b : V) (Lf : LocalTest m) :
    K m (translateLocalTest m b (boostLocalTest m a Lf)) = poincareIsometry m a b (K m Lf) := by
  rw [K_translate_equivariant m b (boostLocalTest m a Lf), K_boost_equivariant m a Lf]
  rfl

/-- **★★★ THE FULL-POINCARÉ PRIZE: the σ-additive localized typicality measure μ∞ is invariant under the
whole connected Poincaré group.**  For a pairwise-spacelike localized family `{K(region i)}`, the typicality
measure is the same as for the family transformed by an arbitrary connected-Poincaré element `U(a,b) = M_b ∘
U₁(a)` (boost `a`, translation `b`).  Since boosts and translations generate the connected Poincaré group of
1+1D Minkowski space, this is full Poincaré covariance of the microcausal typicality measure on the
relativistic free field — the literal Open-Problem-3b deliverable.  Axiom-free. -/
theorem localized_typicality_poincare_invariant (m a : ℝ) (b : V) (region : ι → LocalTest m)
    (hiso : ∀ i j, i ≠ j → Complex.im ⟪K m (region i), K m (region j)⟫_ℂ = 0)
    {μ ν : Measure (∀ _ : ι, Bool)}
    (hμ : (weylBitNet (fun i => K m (region i)) hiso).toFiniteMarginals.IsLimit μ)
    (hν : (weylBitNet (fun i => poincareIsometry m a b (K m (region i)))
            (fun i j hij => by
              rw [LinearIsometry.inner_map_map]; exact hiso i j hij)).toFiniteMarginals.IsLimit ν) :
    μ = ν :=
  weylBit_typicality_boost_invariant (poincareIsometry m a b) (fun i => K m (region i)) hiso
    (fun i j hij => by rw [LinearIsometry.inner_map_map]; exact hiso i j hij) hμ hν

end QIQTH.Fock.Localization
