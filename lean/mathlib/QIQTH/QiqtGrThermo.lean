/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# T3-1 Stage 2 — the thermodynamic free-field QIQT→GR capstone

`qiqt_gr_freefield_geom` takes four labelled thermodynamic premises (`hbound`/`hsat`/`hDnn`/`hD0`).  This file
wires in the finite-entropy witness `clausius_package_from_finite_model`: the entropy/heat functionals are
CONSTRUCTED from a per-generator finite record law `pp` (uniform at the reference), so that

  Sf := Shannon(pp x v t),   KE := Sf + KL(pp x v t ‖ pp x v 0),

and **`hsat`, `hDnn`, `hD0` are discharged internally** — the saturation (given the reference area-capacity
identification `η·A(x,v,0) = log|ι|`) and BOTH relative-entropy facts (positivity + tightness) are now theorems
of the axiom-free finite core, not assumptions.

What stays labelled is exactly the irreducible H2 content: the **dynamical capacity bound** `hbound`
(`Shannon(pp x v t) ≤ η·A x v t` — the FQ holographic bound made dynamical; a fixed record set cannot track a
continuous varying area, so this is the cited continuum frontier) and the **reference identification** `hcap`
(`η·A(x,v,0) = log|ι|`, the FQ postulate at the bifurcation surface), plus the realization derivatives
`hS`/`hK`/`hA` (Gap-2 localization).  See `T3-1_H2_CLAUSIUS_PLAN.md`.

Axiom-free.
-/
import QIQTH.QiqtGrFreeField
import QIQTH.ClausiusFiniteWitness

namespace QIQTH.WedgeKMSToGR

open QIQTH.Curvature QIQTH.QiqtToGR QIQTH.EinsteinEOS
open QIQTH.Fock QIQTH.Fock.OneParticle QIQTH.Fock.BoostKMS QIQTH.Fock.CyclicWitness
  QIQTH.StandardSubspaceModular
open QIQTH.BranchLedger QIQTH.RelEntPositivity QIQTH.RecordContract QIQTH.ClausiusFiniteWitness
open MeasureTheory Filter Topology

/-- **★★★ The THERMODYNAMIC free-field QIQT→GR capstone.**  Einstein's equations for the explicit free
    Klein–Gordon field, with the entropy/heat functionals CONSTRUCTED from a per-generator finite record law
    `pp` (a probability distribution for each deformation `t`, uniform at the equilibrium reference), and the
    saturation + relative-entropy premises (`hsat`/`hDnn`/`hD0`) DISCHARGED internally via
    `clausius_package_from_finite_model` (the axiom-free finite core: Gibbs/Jensen, uniform saturation, classical
    Klein).  Only the genuinely-irreducible H2 inputs survive labelled: the dynamical capacity **bound** `hbound`
    (`Shannon(pp) ≤ η·A`, the holographic FQ bound; the discrete record capacity cannot continuously track the
    varying geometric area — the cited continuum frontier), the reference area-capacity identification `hcap`
    (`η·A(·,·,0) = log|ι|`, the FQ postulate), and the realization derivatives `hS`/`hK`/`hA` (Gap-2).  Every
    modular/BW/boost/stress/focusing/curvature step is machine-checked axiom-free.  No `sorry`. -/
theorem qiqt_gr_freefield_thermo
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (g gi : Point 4 → Fin 4 → Fin 4 → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hCgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (φ : Point 4 → ℝ) (m η hbar a : ℝ)
    (hbar0 : hbar ≠ 0) (heta : η ≠ 0) (ha : a = 2 * Real.pi / (hbar * η))
    (hφ : ContDiff ℝ ⊤ φ) (hKG : ∀ x, boxField φ g gi x = m ^ 2 * φ x)
    (P Pinv : Point 4 → Fin 4 → Fin 4 → ℝ)
    (hPP : ∀ x i j, (∑ k, P x i k * Pinv x k j) = if i = j then (1 : ℝ) else 0)
    (hPP' : ∀ x i j, (∑ k, Pinv x i k * P x k j) = if i = j then (1 : ℝ) else 0)
    (hcong : ∀ x i j, g x i j = ∑ k, ∑ l, P x k i * gm k l * P x l j)
    (A : Point 4 → (Fin 4 → ℝ) → ℝ → ℝ) (sd : Point 4 → (Fin 4 → ℝ) → ℝ)
    -- the per-generator finite record law (uniform at the reference) — Sf/KE are built from it:
    (pp : Point 4 → (Fin 4 → ℝ) → ℝ → ι → ℝ)
    (hpp_nn : ∀ x v t r, 0 ≤ pp x v t r)
    (hpp1 : ∀ x v t, ∑ r, pp x v t r = 1)
    (hpp0 : ∀ x v, pp x v 0 = (fun _ : ι => (Fintype.card ι : ℝ)⁻¹))
    -- the FQ reference area-capacity identification (the holographic postulate at the bifurcation surface):
    (hcap : ∀ x v, η * A x v 0 = Real.log (Fintype.card ι))
    -- the Raychaudhuri congruence (as in `qiqt_gr_freefield_geom`):
    (W : Point 4 → (Fin 4 → ℝ) → Point 4 → Fin 4 → ℝ)
    (hWx : ∀ x v, BL (g x) v = 0 → W x v x = v)
    (hWC : ∀ x v μ, ContDiff ℝ ⊤ (fun y => W x v y μ))
    (hWgeo : ∀ x v, ∀ y μ, (∑ ν, W x v y ν * covDerivVec g gi (W x v) ν μ y) = 0)
    (hWequil : ∀ x v, BL (g x) v = 0 →
        (∑ μ, ∑ ν, covDerivVec g gi (W x v) μ ν x * covDerivVec g gi (W x v) ν μ x) = 0)
    -- realization derivatives of the constructed entropy / heat / area functionals (Gap-2; stay labelled):
    (hS : ∀ x v, BL (g x) v = 0 →
        HasDerivAt (fun t => Shannon Finset.univ (pp x v t)) (sd x v) 0)
    (hK : ∀ x v, BL (g x) v = 0 →
        HasDerivAt (fun t => Shannon Finset.univ (pp x v t) + KL Finset.univ (pp x v t) (pp x v 0))
          (2 * Real.pi / hbar * BL (kgStress m φ g gi x) v) 0)
    (hA : ∀ x v, BL (g x) v = 0 → HasDerivAt (A x v)
        (- ∑ ν, W x v x ν * pd (fun y => expansion g gi (W x v) y) ν x) 0)
    -- the one irreducible thermodynamic input: the dynamical FQ capacity bound:
    (hbound : ∀ x v, BL (g x) v = 0 → ∀ᶠ t in 𝓝 0, Shannon Finset.univ (pp x v t) ≤ η * A x v t)
    (mw : Point 4 → (Fin 4 → ℝ) → ℝ) (hmw : ∀ x v, 0 < mw x v)
    (ff ff' : Point 4 → (Fin 4 → ℝ) → ℝ → ℂ)
    (hf2 : ∀ x v, MemLp (ff x v) 2 (volume : Measure ℝ))
    (hf_int : ∀ x v, Integrable (ff x v) (volume : Measure ℝ))
    (hfd : ∀ x v θ, HasDerivAt (ff x v) (ff' x v θ) θ)
    (hf'_meas : ∀ x v, AEStronglyMeasurable (ff' x v) (volume : Measure ℝ))
    (Bd : Point 4 → (Fin 4 → ℝ) → ℝ) (hB : ∀ x v θ, ‖ff' x v θ‖ ≤ Bd x v)
    (hTkk : ∀ x v, BL (g x) v = 0 →
        (2 * Real.pi / hbar * (∑ b, v b * pd φ b x) ^ 2 : ℝ)
          = (-(2 * Real.pi * ∫ θ, (starRingEnd ℂ) (ff x v θ) * ff' x v θ ∂(volume : Measure ℝ))).im)
    : ∃ Λ : ℝ, ∀ x μ ν, a * kgStress m φ g gi x μ ν = einsteinTensor g gi μ ν x + Λ * g x μ ν := by
  -- the finite-model witness, per generator — supplies hsat/hDnn/hD0:
  have wit := fun x v => clausius_package_from_finite_model (R := ι) η (A x v 0) (pp x v)
    (hpp_nn x v) (hpp1 x v) (hpp0 x v) (hcap x v)
  exact qiqt_gr_freefield_geom g gi hsymm hsymm_gi hinv hCg hCgi φ m η hbar a hbar0 heta ha hφ hKG
    P Pinv hPP hPP' hcong
    (fun x v t => Shannon Finset.univ (pp x v t))
    (fun x v t => Shannon Finset.univ (pp x v t) + KL Finset.univ (pp x v t) (pp x v 0))
    A sd W hWx hWC hWgeo hWequil hS hK hA hbound
    (fun x v _ => (wit x v).2.1)        -- hsat   (uniform saturation)
    (fun x v _ => (wit x v).2.2.1)      -- hDnn   (KE − Sf = KL ≥ 0)
    (fun x v _ => (wit x v).2.2.2)      -- hD0    (KL self = 0)
    mw hmw ff ff' hf2 hf_int hfd hf'_meas Bd hB hTkk

end QIQTH.WedgeKMSToGR
