/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# QIQT→GR capstone with the Raychaudhuri premises from one covariantly-constant condition

`qiqt_gr_freefield_complete` takes the geodesic premise `hWgeo` and the equilibrium premise `hWequil`
separately.  This variant takes the single geometric condition `hcov` ("the congruence `W x v` is covariantly
constant") and DERIVES both via `raychaudhuri_setup_of_covConst` — so the two Raychaudhuri premises collapse to
one clean condition.  Axiom-free.
-/
import QIQTH.QiqtGrComplete
import QIQTH.RaychaudhuriCongruence

namespace QIQTH.WedgeKMSToGR

open QIQTH.Curvature QIQTH.EinsteinEOS QIQTH.RelEntPositivity QIQTH.BranchLedger
  Complex MeasureTheory Real Filter Topology

/-- **The maximally-discharged QIQT→GR capstone with the Raychaudhuri congruence premises reduced to one
    condition.**  Identical to `qiqt_gr_freefield_complete`, but the geodesic premise `hWgeo` and the equilibrium
    premise `hWequil` are replaced by the single condition `hcov` (the congruence `W x v` is covariantly
    constant), from which both are derived (`raychaudhuri_setup_of_covConst`).  Together with the localization
    (T3-3-C3) and entropy (T3-1) discharges, the only surviving labelled inputs are the genuine physics floor
    (`hbound`/`hcap`/`hK`/`hS`/`hA` = H2/FQ + realization), the matter EOM `hKG`, the covariant-constancy
    condition `hcov` (the geometric setup, satisfiable e.g. by any flat or covariantly-constant-null-field
    metric — see `covDerivVec_constMetric_const`), and geometry scaffolding.  Axiom-free. -/
theorem qiqt_gr_freefield_complete_covCong
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
    -- the single geometric condition replacing hWgeo + hWequil:
    (hcov : ∀ x v a b y, covDerivVec g gi (W x v) a b y = 0)
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
  refine qiqt_gr_freefield_complete (ι := ι) g gi hsymm hsymm_gi hinv hCg hCgi φ m η hbar a hbar0 hbar_pos
    heta ha hφ hKG P Pinv hPP hPP' hcong A sd pp hpp_nn hpp1 hpp0 hcap W hWx hWC ?_ ?_ hS hK hA hbound mw hmw
  · exact fun x v => (raychaudhuri_setup_of_covConst g gi (W x v) x (fun a b y => hcov x v a b y)).1
  · exact fun x v _ => (raychaudhuri_setup_of_covConst g gi (W x v) x (fun a b y => hcov x v a b y)).2

end QIQTH.WedgeKMSToGR
