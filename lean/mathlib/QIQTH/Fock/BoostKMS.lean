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

end QIQTH.Fock.BoostKMS
