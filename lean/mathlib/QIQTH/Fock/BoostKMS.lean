/-
  A4 (QIQT_GR_DISCHARGE_PLAN.md) — assembling `StripKMSrvd(boostUnitary, 𝒦_W)` from the wedge-mode
  analytic continuation (`WedgeAnalyticity`). This file bridges the concrete rapidity integrals to the
  abstract `Lp ℂ 2` inner product and the `boostUnitary` (rapidity-translation) action.

  First increment: the `L²` inner product of two wedge modes as a concrete `∫…dθ`, and its boosted form
  `⟪η, boostUnitary a ξ⟫ = ∫ conj(Krep g θ)·Krep f (θ−a) dθ` — the real-axis edge of the KMS function.
-/
import QIQTH.Fock.OneParticleBW
import QIQTH.Fock.WedgeAnalyticity

noncomputable section

open MeasureTheory Complex

namespace QIQTH.Fock.BoostKMS

open QIQTH.Fock.Localization QIQTH.Fock.OneParticle QIQTH.Fock.OneParticleBW QIQTH.Fock.WedgeAnalyticity

/-- **The `L²` inner product of two wedge modes as a concrete rapidity integral.**
    `⟪KrepL2 f, KrepL2 g⟫ = ∫ conj(Krep m f θ)·Krep m g θ dθ` (via `L2.inner_def` + `MemLp.coeFn_toLp`). -/
theorem inner_KrepL2 (m : ℝ) {f g : V → ℂ} (hf : MemLp (Krep m f) 2 volume)
    (hg : MemLp (Krep m g) 2 volume) :
    inner ℂ (hf.toLp (Krep m f)) (hg.toLp (Krep m g))
      = ∫ θ, (starRingEnd ℂ) (Krep m f θ) * Krep m g θ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with θ hfθ hgθ
  rw [hfθ, hgθ, RCLike.inner_apply]; ring

/-- **The real-axis edge.** `⟪KrepL2 g, boostUnitary a (KrepL2 f)⟫ = ∫ conj(Krep m g θ)·Krep m f (θ−a) dθ`.
    Combines `boostUnitary_KrepL2` (boost acts by `boostTest`), `inner_KrepL2`, and the amplitude boost-
    covariance `Krep m (boostTest (−a) f) θ = Krep m f (θ−a)`. This is the orbit correlation `f(t) =
    ⟪η, V_t ξ⟫` of `StripKMSrvd` (with `V_t = boostUnitary a`, `a` the rapidity). -/
theorem inner_boostUnitary_KrepL2 (m a : ℝ) {f g : V → ℂ}
    (hf : MemLp (Krep m f) 2 volume) (hg : MemLp (Krep m g) 2 volume)
    (hbf : MemLp (Krep m (boostTest (-a) f)) 2 volume) :
    inner ℂ (hg.toLp (Krep m g)) (boostUnitary a (hf.toLp (Krep m f)))
      = ∫ θ, (starRingEnd ℂ) (Krep m g θ) * Krep m f (θ - a) := by
  rw [boostUnitary_KrepL2 m a f hf hbf, inner_KrepL2 m hg hbf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only [Krep_boost]
  rw [sub_eq_add_neg]

/-- **Symmetric ↔ shifted edge (change of variables `θ ↦ θ+πt`).** The KMS function's symmetric real-axis
    form equals the boost-orbit form:
    `∫ conj(Krep g (θ+πt))·Krep f (θ−πt) dθ = ∫ conj(Krep g θ)·Krep f (θ−2πt) dθ` (translation invariance). -/
theorem symm_edge_eq_shifted (m t : ℝ) (f g : V → ℂ) :
    (∫ θ, (starRingEnd ℂ) (Krep m g (θ + Real.pi * t)) * Krep m f (θ - Real.pi * t))
      = ∫ θ, (starRingEnd ℂ) (Krep m g θ) * Krep m f (θ - 2 * Real.pi * t) := by
  rw [← MeasureTheory.integral_add_right_eq_self
    (fun θ => (starRingEnd ℂ) (Krep m g θ) * Krep m f (θ - 2 * Real.pi * t)) (Real.pi * t)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only []
  rw [show θ - Real.pi * t = θ + Real.pi * t - 2 * Real.pi * t from by ring]

/-- **The KMS top edge `f(t) = ⟪η, V_t ξ⟫` in symmetric (KMS-function) form.** Combining `symm_edge_eq_shifted`
    and `inner_boostUnitary_KrepL2`: the symmetric integral `∫ conj(Krep g (θ+πt))·Krep f (θ−πt) dθ` — the
    `t`-real value of the KMS function `F(z)=∫ conj(KrepCont g (θ+πz̄))·KrepCont f (θ−πz)` — equals
    `⟪KrepL2 g, boostUnitary(2πt) (KrepL2 f)⟫`. (Boost sign `+2π` here; `StripKMSrvd`'s `V_t=boostUnitary(−2π·)`
    is matched by orienting `t`.) -/
theorem symm_edge_eq_inner (m t : ℝ) {f g : V → ℂ}
    (hf : MemLp (Krep m f) 2 volume) (hg : MemLp (Krep m g) 2 volume)
    (hbf : MemLp (Krep m (boostTest (-(2 * Real.pi * t)) f)) 2 volume) :
    (∫ θ, (starRingEnd ℂ) (Krep m g (θ + Real.pi * t)) * Krep m f (θ - Real.pi * t))
      = inner ℂ (hg.toLp (Krep m g)) (boostUnitary (2 * Real.pi * t) (hf.toLp (Krep m f))) := by
  rw [symm_edge_eq_shifted, inner_boostUnitary_KrepL2 m (2 * Real.pi * t) hf hg hbf]

/-- **The KMS function** `F(z) = ∫ conj(KrepCont g (conj(θ+πz)))·KrepCont f (θ−πz) dθ` — the candidate
    `StripKMSrvd` witness. `H^#(θ+πz) = conj(H(conj(θ+πz)))` with `H = KrepCont g`, `Ξ = KrepCont f`; for `z`
    in the strip `{−1<Im z<0}` both factors are evaluated with imaginary part in `(0,π)` (the good damping
    region). -/
def kmsFun (m : ℝ) (f g : V → ℂ) (z : ℂ) : ℂ :=
  ∫ θ : ℝ, (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
    * KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)

/-- **The KMS function on the real axis** equals the symmetric integral (via `KrepCont_ofReal`): the real-axis
    arguments are real, so each `KrepCont` collapses to `Krep` and the inner conjugation is trivial. -/
theorem kmsFun_ofReal (m : ℝ) (f g : V → ℂ) (t : ℝ) :
    kmsFun m f g (t : ℂ)
      = ∫ θ, (starRingEnd ℂ) (Krep m g (θ + Real.pi * t)) * Krep m f (θ - Real.pi * t) := by
  rw [kmsFun]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  have e1 : (θ : ℂ) + (Real.pi : ℂ) * (t : ℂ) = ((θ + Real.pi * t : ℝ) : ℂ) := by push_cast; ring
  have e2 : (θ : ℂ) - (Real.pi : ℂ) * (t : ℂ) = ((θ - Real.pi * t : ℝ) : ℂ) := by push_cast; ring
  simp only [e1, e2, Complex.conj_ofReal, KrepCont_ofReal]

/-- **The KMS top edge for `kmsFun`**: `F(t) = ⟪KrepL2 g, boostUnitary(2πt) (KrepL2 f)⟫`
    (`kmsFun_ofReal` ∘ `symm_edge_eq_inner`). -/
theorem kmsFun_ofReal_eq_inner (m t : ℝ) {f g : V → ℂ}
    (hf : MemLp (Krep m f) 2 volume) (hg : MemLp (Krep m g) 2 volume)
    (hbf : MemLp (Krep m (boostTest (-(2 * Real.pi * t)) f)) 2 volume) :
    kmsFun m f g (t : ℂ)
      = inner ℂ (hg.toLp (Krep m g)) (boostUnitary (2 * Real.pi * t) (hf.toLp (Krep m f))) := by
  rw [kmsFun_ofReal, symm_edge_eq_inner m t hf hg hbf]

/-- **The KMS bottom edge `F(t−i) = conj(F(t))`** (for real `f,g`). At `z=t−i` the `iπ`-shift puts both
    `KrepCont` arguments at imaginary part `+π`, so `KrepCont_add_pi_I` (A3) collapses each to `conj(Krep …)`:
    `F(t−i) = ∫ Krep g(θ+πt)·conj(Krep f(θ−πt)) dθ = conj(F(t))`. With the top edge (`kmsFun_ofReal_eq_inner`)
    and `⟪V_t ξ,η⟫ = conj⟪η,V_t ξ⟫`, this is the bottom-edge requirement `f(t−i) = ⟪V_t ξ,η⟫` of `StripKMSrvd`. -/
theorem kmsFun_sub_I (m : ℝ) {f g : V → ℂ} (hfr : ∀ x, (starRingEnd ℂ) (f x) = f x)
    (hgr : ∀ x, (starRingEnd ℂ) (g x) = g x) (t : ℝ) :
    kmsFun m f g ((t : ℂ) - Complex.I) = (starRingEnd ℂ) (kmsFun m f g (t : ℂ)) := by
  have hL : kmsFun m f g ((t : ℂ) - Complex.I)
      = ∫ θ, Krep m g (θ + Real.pi * t) * (starRingEnd ℂ) (Krep m f (θ - Real.pi * t)) := by
    rw [kmsFun]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    dsimp only
    have ag : (starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * ((t : ℂ) - Complex.I))
        = ((θ + Real.pi * t : ℝ) : ℂ) + (Real.pi : ℂ) * Complex.I := by
      simp only [map_add, map_mul, map_sub, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    have af : (θ : ℂ) - (Real.pi : ℂ) * ((t : ℂ) - Complex.I)
        = ((θ - Real.pi * t : ℝ) : ℂ) + (Real.pi : ℂ) * Complex.I := by push_cast; ring
    rw [ag, af, KrepCont_add_pi_I m hgr, KrepCont_add_pi_I m hfr, Complex.conj_conj]
  rw [hL, kmsFun_ofReal, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only [map_mul, Complex.conj_conj, mul_comm]

/-- **The reflected amplitude `u ↦ conj(KrepCont g(conj u))` is entire** (Schwarz reflection: `conj∘F∘conj`
    is holomorphic when `F` is). Via `DifferentiableAt.star_conj` + `differentiable_KrepCont`. This is the `g`
    factor `H^#` of the KMS-function integrand — the holomorphy ingredient for `kmsFun`. -/
theorem differentiable_reflKrepCont (m : ℝ) {g : V → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    Differentiable ℂ (fun u : ℂ => (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) u))) := by
  have hg' : Differentiable ℂ (KrepCont m g) := differentiable_KrepCont m hg hgc
  intro z
  have h := (hg' ((starRingEnd ℂ) z)).star_conj
  rw [Complex.conj_conj] at h
  exact h

/-- The derivative of the reflected amplitude: `deriv(u ↦ conj(KrepCont g(conj u))) u
    = conj(deriv(KrepCont g)(conj u))` (Schwarz reflection, `HasDerivAt.conj_conj`). -/
theorem deriv_reflKrepCont_eq (m : ℝ) {g : V → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (u : ℂ) :
    deriv (fun u => (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) u))) u
      = (starRingEnd ℂ) (deriv (KrepCont m g) ((starRingEnd ℂ) u)) := by
  have hd : HasDerivAt (KrepCont m g) (deriv (KrepCont m g) ((starRingEnd ℂ) u)) ((starRingEnd ℂ) u) :=
    (differentiable_KrepCont m hg hgc ((starRingEnd ℂ) u)).hasDerivAt
  have h := hd.conj_conj
  rw [Complex.conj_conj] at h
  exact h.deriv

/-- **The `kmsFun` integrand is entire in `z`** (for `f,g` continuous with compact support). The `g`-factor
    `conj(KrepCont g(conj(θ+πz)))` = `differentiable_reflKrepCont ∘ (affine)`, the `f`-factor `KrepCont f(θ−πz)`
    = `differentiable_KrepCont ∘ (affine)`; the product is differentiable. This is the per-`θ` (`h_diff`)
    ingredient for the parametric-integral holomorphy of `F` (`DiffContOnCl`). -/
theorem differentiable_kmsIntegrand (m : ℝ) {f g : V → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (θ : ℝ) :
    Differentiable ℂ (fun z : ℂ =>
      (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
        * KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)) :=
  ((differentiable_reflKrepCont m hg hgc).comp (by fun_prop)).mul
    ((differentiable_KrepCont m hf hfc).comp (by fun_prop))

/-- **The `kmsFun` integrand is continuous in `θ`** (for fixed `z`) — the measurability (`hF_meas`) ingredient
    for the parametric-integral holomorphy of `F`. `KrepCont` is continuous (entire), composed with the
    continuous `θ`-maps `θ↦conj(θ+πz)`, `θ↦θ−πz`, and `conj`. -/
theorem continuous_kmsIntegrand_in_theta (m : ℝ) {f g : V → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hg : Continuous g) (hgc : HasCompactSupport g) (z : ℂ) :
    Continuous (fun θ : ℝ =>
      (starRingEnd ℂ) (KrepCont m g ((starRingEnd ℂ) ((θ : ℂ) + (Real.pi : ℂ) * z)))
        * KrepCont m f ((θ : ℂ) - (Real.pi : ℂ) * z)) :=
  (Complex.continuous_conj.comp ((differentiable_KrepCont m hg hgc).continuous.comp
      (Complex.continuous_conj.comp (by fun_prop)))).mul
    ((differentiable_KrepCont m hf hfc).continuous.comp (by fun_prop))

/-- **★★★★ `StripKMSrvd` for a wedge generator pair, reduced to the analytic regularity of `kmsFun`.**
    For real wedge modes `ξ=KrepL2 f`, `η=KrepL2 g`, GIVEN only that the explicit KMS function `kmsFun m f g`
    is `DiffContOnCl` on the strip `{−1<Im z<0}` and bounded (`hDCC`, `hbd`), the `StripKMSrvd` `∃F` witness
    holds for this pair with `V_t = boostUnitary(2πt)`: `F=kmsFun`, top edge `F(t)=⟪η,V_t ξ⟫`
    (`kmsFun_ofReal_eq_inner`), bottom edge `F(t−i)=⟪V_t ξ,η⟫` (`kmsFun_sub_I` + `inner_conj_symm`).

    This **precisely isolates the entire remaining frontier** of the free-field BW/Hardy discharge: everything
    — the construction of `F`, both KMS edges, the `Lp` bridge, the boost-orbit identification — is DONE and
    axiom-free; what remains is the analytic regularity (`DiffContOnCl` + boundedness) of the single explicit
    function `kmsFun m f g`, of which the holomorphy ingredients (`differentiable_kmsIntegrand`,
    `continuous_kmsIntegrand_in_theta`, `integrable_cosh_mul_exp_neg_const_mul_cosh`) are in hand. -/
theorem stripKMSrvd_pair_of_regularity (m : ℝ) {f g : V → ℂ}
    (hf : MemLp (Krep m f) 2 volume) (hg : MemLp (Krep m g) 2 volume)
    (hbf : ∀ t : ℝ, MemLp (Krep m (boostTest (-(2 * Real.pi * t)) f)) 2 volume)
    (hfr : ∀ x, (starRingEnd ℂ) (f x) = f x) (hgr : ∀ x, (starRingEnd ℂ) (g x) = g x)
    (hDCC : DiffContOnCl ℂ (kmsFun m f g) (Complex.im ⁻¹' Set.Ioo (-1 : ℝ) 0))
    (hbd : ∃ M : ℝ, ∀ z : ℂ, ‖kmsFun m f g z‖ ≤ M) :
    ∃ F : ℂ → ℂ, DiffContOnCl ℂ F (Complex.im ⁻¹' Set.Ioo (-1 : ℝ) 0) ∧
      (∃ M : ℝ, ∀ z : ℂ, ‖F z‖ ≤ M) ∧
      (∀ t : ℝ, F t = inner ℂ (hg.toLp (Krep m g)) (boostUnitary (2 * Real.pi * t) (hf.toLp (Krep m f)))) ∧
      (∀ t : ℝ, F ((t : ℂ) - Complex.I)
        = inner ℂ (boostUnitary (2 * Real.pi * t) (hf.toLp (Krep m f))) (hg.toLp (Krep m g))) := by
  refine ⟨kmsFun m f g, hDCC, hbd, fun t => kmsFun_ofReal_eq_inner m t hf hg (hbf t), fun t => ?_⟩
  rw [kmsFun_sub_I m hfr hgr t, kmsFun_ofReal_eq_inner m t hf hg (hbf t)]
  exact inner_conj_symm _ _

end QIQTH.Fock.BoostKMS
