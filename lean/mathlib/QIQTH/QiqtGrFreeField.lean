/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The FREE-FIELD QIQT→GR capstone

`QIQT_GR_FREEFIELD_COMPLETION_PLAN.md`, Phases 4–5.  Assembles the Einstein equations for the explicit free
Klein–Gordon field with the wedge-KMS modular flux supplied by the axiom-free `+2π` one-particle machinery
(`Fock/FreeFieldHFlux.lean`) instead of the labelled `WedgeKMSFlux_complete` bundle.

`freeField_kd_conclusion` is the `∀`-wrap of `freeField_component_hFlux`: from a per-null-generator localization
datum it produces the flux equation `kd x v = (2π/ℏ)·BL(T x)v` that `qiqt_gr_from_flux_complete` consumes.

`qiqt_gr_freefield` then mirrors `qiqt_gr_explicit_kg` (geometry `hC`/`hric_symm`/`hreg`/`conserv` all discharged
internally for `kgStress`) with the modular input now the free-field localization datum.  The only labelled inputs
are the Clausius/area-saturation physics + the per-generator localization map `(hbridge, hTkk)` (Gap 2).

Axiom-free.
-/
import QIQTH.QiqtGrExplicitKG
import QIQTH.Fock.FreeFieldHFlux

namespace QIQTH.WedgeKMSToGR

open QIQTH.Curvature QIQTH.QiqtToGR QIQTH.EinsteinEOS
open QIQTH.Fock QIQTH.Fock.OneParticle QIQTH.Fock.BoostKMS QIQTH.Fock.CyclicWitness
  QIQTH.StandardSubspaceModular
open MeasureTheory Filter Topology

/-- **★★★ The free-field flux equation `kd x v = (2π/ℏ)·BL(T x)v`, per null generator.**  The `∀`-wrap of
    `freeField_component_hFlux`: given, for each null horizon generator `(x,v)`, a smooth wedge mode `f_{x,v}`
    (with the standard integrability/measurability/bound data) together with
    - `hbridge` : the abstract coefficient `kd x v` IS the modular energy of the localized mode, and
    - `hTkk` : the localization identification of `BL(T x)v` with the mode's rapidity stress flux,
    derivative uniqueness against the axiom-free `freeField_oneParticle_hFlux` yields the flux equation.  This is the
    exact input `qiqt_gr_from_flux_complete` (hence `qiqt_bekenstein_gives_gr`) consumes.  Everything
    modular/BW/boost/stress is machine-checked; the per-generator `(hbridge, hTkk)` are the localization map (Gap 2). -/
theorem freeField_kd_conclusion
    (g T : Point 4 → Fin 4 → Fin 4 → ℝ) (kd : Point 4 → (Fin 4 → ℝ) → ℝ) (hbar : ℝ)
    (mw : Point 4 → (Fin 4 → ℝ) → ℝ) (hmw : ∀ x v, 0 < mw x v)
    (f f' : Point 4 → (Fin 4 → ℝ) → ℝ → ℂ)
    (hf2 : ∀ x v, MemLp (f x v) 2 (volume : Measure ℝ))
    (hf_int : ∀ x v, Integrable (f x v) (volume : Measure ℝ))
    (hF0_int : ∀ x v, Integrable (fun θ => (starRingEnd ℂ) (f x v θ) * f x v θ) (volume : Measure ℝ))
    (hfd : ∀ x v θ, HasDerivAt (f x v) (f' x v θ) θ)
    (hf'_meas : ∀ x v, AEStronglyMeasurable (f' x v) (volume : Measure ℝ))
    (B : Point 4 → (Fin 4 → ℝ) → ℝ) (hB : ∀ x v θ, ‖f' x v θ‖ ≤ B x v)
    (hTkk : ∀ x v, BL (g x) v = 0 →
        (2 * Real.pi / hbar * BL (T x) v : ℝ)
          = (-(2 * Real.pi * ∫ θ, (starRingEnd ℂ) (f x v θ) * f' x v θ ∂(volume : Measure ℝ))).im)
    (hbridge : ∀ x v, BL (g x) v = 0 → HasDerivAt
        (fun t : ℝ => inner ℂ ((hf2 x v).toLp (f x v))
          (modUnitary (niceWedgeStandardSubspace (mw x v)
            (niceWedge_isSeparating_of_no_complex_line (mw x v) (niceWedgeSeparating_pos_mass (hmw x v)))
            (niceWedge_isCyclic_of_total_integral (mw x v) (niceWedgeCyclic_pos_mass (hmw x v)))) t
            ((hf2 x v).toLp (f x v))))
        (Complex.I * ((kd x v : ℝ) : ℂ)) 0) :
    ∀ x v, BL (g x) v = 0 → kd x v = 2 * Real.pi / hbar * BL (T x) v := by
  intro x v hnull
  exact freeField_component_hFlux (hmw x v) (f x v) (f' x v) (hf2 x v) (hf_int x v) (hF0_int x v)
    (hfd x v) (hf'_meas x v) (B x v) (hB x v) hbar (kd x v) (BL (T x) v)
    (hTkk x v hnull) (hbridge x v hnull)

/-- **★★★★★★ THE FREE-FIELD QIQT→GR CAPSTONE.**  Einstein's equations for the explicit free Klein–Gordon field,
    with the wedge-KMS modular flux supplied entirely by the axiom-free `+2π` one-particle Bisognano–Wichmann
    machinery — NOT a labelled `WedgeKMSFlux_complete` bundle.  Identical to `qiqt_gr_explicit_kg` (geometry
    `hC`/`hric_symm`/`hreg`, matter `conserv`, and `hT_symm` all discharged internally for `kgStress`), but the
    modular input is the per-null-generator localization datum `(mw, f, f', …, hTkk, hbridge)` feeding
    `freeField_kd_conclusion`.  Of the GR chain's inputs only the genuine physics survives labelled: the
    Clausius/area-saturation law (`hbound`/`hsat`/`hDnn`/`hD0`), the focusing identity `hFocus`, and the
    per-generator localization map `(hbridge, hTkk)` (Gap 2 — the dynamical realization of horizon generators by
    wedge modes).  Every modular, Bisognano–Wichmann, boost-charge, stress-flux, conservation, and curvature step is
    machine-checked axiom-free.  No `sorry`. -/
theorem qiqt_gr_freefield
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
    (Sf KE A : Point 4 → (Fin 4 → ℝ) → ℝ → ℝ) (sd kd ad : Point 4 → (Fin 4 → ℝ) → ℝ)
    (hS : ∀ x v, BL (g x) v = 0 → HasDerivAt (Sf x v) (sd x v) 0)
    (hK : ∀ x v, BL (g x) v = 0 → HasDerivAt (KE x v) (kd x v) 0)
    (hA : ∀ x v, BL (g x) v = 0 → HasDerivAt (A x v) (ad x v) 0)
    (hbound : ∀ x v, BL (g x) v = 0 → ∀ᶠ t in 𝓝 0, Sf x v t ≤ η * A x v t)
    (hsat : ∀ x v, BL (g x) v = 0 → Sf x v 0 = η * A x v 0)
    (hDnn : ∀ x v, BL (g x) v = 0 → ∀ t, 0 ≤ KE x v t - Sf x v t)
    (hD0 : ∀ x v, BL (g x) v = 0 → KE x v 0 - Sf x v 0 = 0)
    -- the free-field localization datum (replaces the labelled `WedgeKMSFlux_complete` bundle):
    (mw : Point 4 → (Fin 4 → ℝ) → ℝ) (hmw : ∀ x v, 0 < mw x v)
    (ff ff' : Point 4 → (Fin 4 → ℝ) → ℝ → ℂ)
    (hf2 : ∀ x v, MemLp (ff x v) 2 (volume : Measure ℝ))
    (hf_int : ∀ x v, Integrable (ff x v) (volume : Measure ℝ))
    (hF0_int : ∀ x v, Integrable (fun θ => (starRingEnd ℂ) (ff x v θ) * ff x v θ) (volume : Measure ℝ))
    (hfd : ∀ x v θ, HasDerivAt (ff x v) (ff' x v θ) θ)
    (hf'_meas : ∀ x v, AEStronglyMeasurable (ff' x v) (volume : Measure ℝ))
    (Bd : Point 4 → (Fin 4 → ℝ) → ℝ) (hB : ∀ x v θ, ‖ff' x v θ‖ ≤ Bd x v)
    (hTkk : ∀ x v, BL (g x) v = 0 →
        (2 * Real.pi / hbar * BL (kgStress m φ g gi x) v : ℝ)
          = (-(2 * Real.pi * ∫ θ, (starRingEnd ℂ) (ff x v θ) * ff' x v θ ∂(volume : Measure ℝ))).im)
    (hbridge : ∀ x v, BL (g x) v = 0 → HasDerivAt
        (fun t : ℝ => inner ℂ ((hf2 x v).toLp (ff x v))
          (modUnitary (niceWedgeStandardSubspace (mw x v)
            (niceWedge_isSeparating_of_no_complex_line (mw x v) (niceWedgeSeparating_pos_mass (hmw x v)))
            (niceWedge_isCyclic_of_total_integral (mw x v) (niceWedgeCyclic_pos_mass (hmw x v)))) t
            ((hf2 x v).toLp (ff x v))))
        (Complex.I * ((kd x v : ℝ) : ℂ)) 0)
    (hFocus : ∀ x v, BL (g x) v = 0 → ad x v = BL (fun i j => ricci g gi i j x) v)
    : ∃ Λ : ℝ, ∀ x μ ν, a * kgStress m φ g gi x μ ν = einsteinTensor g gi μ ν x + Λ * g x μ ν := by
  -- `hC`, `hric_symm`, `hreg` are theorems (Tier A5/A1/A4), supplied internally:
  -- hC, hric_symm now discharged INSIDE qiqt_gr_from_flux_complete (no longer passed):
  have hreg : ∀ f : Point 4 → ℝ,
      (∀ y a' b, a * kgStress m φ g gi y a' b = ricci g gi a' b y + f y * g y a' b) →
      (∀ x ρ, PdiffAt f ρ x) ∧
        Differentiable ℝ (fun y => f y + (1 / 2 : ℝ) * scalarCurv g gi y) :=
    fun f hrel => hreg_kg m φ g gi a hsymm_gi hinv hφ hCg hCgi f hrel
  refine qiqt_gr_from_flux_complete g gi hsymm hsymm_gi hinv hCg hCgi
    (kgStress m φ g gi) η hbar a hbar0 heta ha ?_ P Pinv hPP hPP' hcong
    Sf KE A sd kd ad hS hK hA hbound hsat hDnn hD0
    (freeField_kd_conclusion g (kgStress m φ g gi) kd hbar mw hmw ff ff' hf2 hf_int hF0_int
      hfd hf'_meas Bd hB hTkk hbridge) hFocus hreg ?_
  · -- `kgStress` is symmetric
    intro x a' b
    simp only [kgStress]
    rw [hsymm x a' b]; ring
  · -- `conserv` discharged internally for the explicit KG field
    intro x ν
    exact kg_conserv_of_contDiff a m φ g gi x ν hsymm hsymm_gi hinv hφ hCg hCgi (hKG x)

end QIQTH.WedgeKMSToGR
