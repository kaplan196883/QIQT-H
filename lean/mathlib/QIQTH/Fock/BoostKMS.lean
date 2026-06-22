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

end QIQTH.Fock.BoostKMS
