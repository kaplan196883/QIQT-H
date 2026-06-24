/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The maximally-discharged free-field QIQT→GR capstone

Combines BOTH discharge programs on the shared base:
* T3-1 (`thermo`): entropy/heat built from a finite record law ⇒ `hsat`/`hDnn`/`hD0` discharged;
* T3-3 (`gaussian`/C3): the wedge mode built from φ ⇒ `hTkk` and the whole `ff` regularity block discharged;
* plus the earlier ladder (`hbridge`/`hFocus`/`hWarea`).

So Einstein's equations `a·kgStress = G + Λg` follow with the localization map CONSTRUCTED from φ and the
relative-entropy/saturation premises PROVED from the finite core.  The only labelled inputs that survive are the
genuinely-irreducible ones: the dynamical FQ capacity bound `hbound`, the FQ reference identification `hcap`,
the heat/entropy/area realization derivatives `hS`/`hK`/`hA`, and the Raychaudhuri congruence setup
`hWx`/`hWC`/`hWgeo`/`hWequil` (geodesic-ODE frontier) — together with the geometry scaffolding and matter EOM
`hKG`.  Axiom-free.
-/
import QIQTH.QiqtGrThermo
import QIQTH.GaussianMode

namespace QIQTH.WedgeKMSToGR

open QIQTH.Curvature QIQTH.EinsteinEOS QIQTH.RelEntPositivity QIQTH.BranchLedger
  Complex MeasureTheory Real Filter Topology

/-- **★★★★★★ The maximally-discharged free-field QIQT→GR capstone.**  Einstein's equations for the explicit free
    Klein–Gordon field, with the entropy/heat functionals built from a finite record law (T3-1, discharging
    `hsat`/`hDnn`/`hD0`) AND the wedge mode built from φ as `↑(∑ₐ vₐ ∂ₐφ)·gaussMode ℏ` (T3-3-C3, discharging
    `hTkk` and the whole `ff` regularity block), on top of the `hbridge`/`hFocus`/`hWarea`-discharged ladder.
    Surviving labelled inputs: the dynamical FQ capacity bound `hbound`, the FQ reference identification `hcap`,
    the realization derivatives `hS`/`hK`/`hA`, the Raychaudhuri congruence setup, geometry scaffolding, and the
    matter EOM `hKG`.  Axiom-free. -/
theorem qiqt_gr_freefield_complete
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (g gi : Point 4 → Fin 4 → Fin 4 → ℝ)
    (hsymm : ∀ y a b, g y a b = g y b a) (hsymm_gi : ∀ y a b, gi y a b = gi y b a)
    (hinv : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hCg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hCgi : ∀ a b, ContDiff ℝ ⊤ (fun y => gi y a b))
    (φ : Point 4 → ℝ) (m η hbar a : ℝ)
    (hbar0 : hbar ≠ 0) (hbar_pos : 0 < hbar) (heta : η ≠ 0) (ha : a = 2 * Real.pi / (hbar * η))
    (hφ : ContDiff ℝ ⊤ φ) (hKG : ∀ x, boxField φ g gi x = m ^ 2 * φ x)
    (P Pinv : Point 4 → Fin 4 → Fin 4 → ℝ)
    (hPP : ∀ x i j, (∑ k, P x i k * Pinv x k j) = if i = j then (1 : ℝ) else 0)
    (hPP' : ∀ x i j, (∑ k, Pinv x i k * P x k j) = if i = j then (1 : ℝ) else 0)
    (hcong : ∀ x i j, g x i j = ∑ k, ∑ l, P x k i * gm k l * P x l j)
    (A : Point 4 → (Fin 4 → ℝ) → ℝ → ℝ) (sd : Point 4 → (Fin 4 → ℝ) → ℝ)
    (pp : Point 4 → (Fin 4 → ℝ) → ℝ → ι → ℝ)
    (hpp_nn : ∀ x v t r, 0 ≤ pp x v t r)
    (hpp1 : ∀ x v t, ∑ r, pp x v t r = 1)
    (hpp0 : ∀ x v, pp x v 0 = (fun _ : ι => (Fintype.card ι : ℝ)⁻¹))
    (hcap : ∀ x v, η * A x v 0 = Real.log (Fintype.card ι))
    (W : Point 4 → (Fin 4 → ℝ) → Point 4 → Fin 4 → ℝ)
    (hWx : ∀ x v, BL (g x) v = 0 → W x v x = v)
    (hWC : ∀ x v μ, ContDiff ℝ ⊤ (fun y => W x v y μ))
    (hWgeo : ∀ x v, ∀ y μ, (∑ ν, W x v y ν * covDerivVec g gi (W x v) ν μ y) = 0)
    (hWequil : ∀ x v, BL (g x) v = 0 →
        (∑ μ, ∑ ν, covDerivVec g gi (W x v) μ ν x * covDerivVec g gi (W x v) ν μ x) = 0)
    (hS : ∀ x v, BL (g x) v = 0 →
        HasDerivAt (fun t => Shannon Finset.univ (pp x v t)) (sd x v) 0)
    (hK : ∀ x v, BL (g x) v = 0 →
        HasDerivAt (fun t => Shannon Finset.univ (pp x v t) + KL Finset.univ (pp x v t) (pp x v 0))
          (2 * Real.pi / hbar * BL (kgStress m φ g gi x) v) 0)
    (hA : ∀ x v, BL (g x) v = 0 → HasDerivAt (A x v)
        (- ∑ ν, W x v x ν * pd (fun y => expansion g gi (W x v) y) ν x) 0)
    (hbound : ∀ x v, BL (g x) v = 0 → ∀ᶠ t in 𝓝 0, Shannon Finset.univ (pp x v t) ≤ η * A x v t)
    (mw : Point 4 → (Fin 4 → ℝ) → ℝ) (hmw : ∀ x v, 0 < mw x v)
    : ∃ Λ : ℝ, ∀ x μ ν, a * kgStress m φ g gi x μ ν = einsteinTensor g gi μ ν x + Λ * g x μ ν := by
  refine qiqt_gr_freefield_thermo (ι := ι) g gi hsymm hsymm_gi hinv hCg hCgi φ m η hbar a hbar0 heta ha hφ hKG
    P Pinv hPP hPP' hcong A sd pp hpp_nn hpp1 hpp0 hcap W hWx hWC hWgeo hWequil hS hK hA hbound mw hmw
    (fun x v θ => ((∑ b, v b * pd φ b x : ℝ) : ℂ) * gaussMode hbar θ)
    (fun x v θ => ((∑ b, v b * pd φ b x : ℝ) : ℂ) * gaussMode' hbar θ)
    (fun x v => (gaussMode_memLp hbar).const_mul ((∑ b, v b * pd φ b x : ℝ) : ℂ))
    (fun x v => (gaussMode_integrable_fn hbar hbar_pos).const_mul ((∑ b, v b * pd φ b x : ℝ) : ℂ))
    (fun x v θ => (gaussMode_hasDerivAt hbar θ).const_mul ((∑ b, v b * pd φ b x : ℝ) : ℂ))
    (fun x v => (continuous_const.mul (gaussMode'_continuous hbar)).aestronglyMeasurable)
    (fun x v => |∑ b, v b * pd φ b x| * gaussC hbar)
    (fun x v θ => ?_)
    (fun x v _ => localized_mode_hTkk φ x v hbar (gaussMode hbar) (gaussMode' hbar)
      (gaussMode_calibration hbar hbar_pos))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (gaussMode'_norm_le hbar hbar_pos θ) (abs_nonneg _)

end QIQTH.WedgeKMSToGR
