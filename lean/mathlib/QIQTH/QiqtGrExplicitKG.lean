/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# QIQT→GR for the EXPLICIT free Klein–Gordon field

The top-level QIQT→GR theorem `qiqt_gr_from_wedge_kms_complete` derives the Einstein field equations for an
*abstract* matter stress tensor `T`, taking `conserv : ∇·(a·T)=0` as a hypothesis.  Here we specialise `T` to the
*explicit* free Klein–Gordon stress tensor `kgStress`, so that `conserv` is no longer a free hypothesis — it is
discharged internally by `kg_conserv_of_contDiff` (from `ContDiff` smoothness + the equation of motion `□φ=m²φ`),
and the stress-tensor symmetry `hT_symm` is proved from metric symmetry.  The result is the QIQT→GR Einstein
equations for a concrete smooth scalar field, with the matter-conservation and stress-tensor inputs eliminated.

Axiom-free.
-/
import QIQTH.WedgeKMSToGR
import QIQTH.KGStressConservation
import QIQTH.RicciSymm
import QIQTH.ChristoffelSmooth
import QIQTH.HregExplicitKG

namespace QIQTH.WedgeKMSToGR

open QIQTH.Curvature QIQTH.QiqtToGR QIQTH.EinsteinEOS
open Filter Topology

/-- **★★★★★★★ THE QIQT→GR EINSTEIN EQUATIONS FOR THE EXPLICIT FREE KLEIN–GORDON FIELD, axiom-free.**
    Specialising the abstract `qiqt_gr_from_wedge_kms_complete` to `T = kgStress` (the concrete KG stress tensor):
    the matter-conservation input `conserv` is discharged INTERNALLY (`kg_conserv_of_contDiff`, from `ContDiff`
    smoothness of `φ, g, gi` + the equation of motion `□φ = m²φ`), and the stress-tensor symmetry is proved from
    metric symmetry.  So for a smooth free scalar `φ` on a smooth Lorentzian metric, given the genuinely physical
    inputs (the Clausius/area-saturation law `hbound`/`hsat`, the wedge-KMS flux `hKMS`, Raychaudhuri focusing
    `hFocus`, and the equation of motion), the Einstein field equations
    `a·T_{μν} = G_{μν} + Λ·g_{μν}` hold for the explicit Klein–Gordon stress tensor.  No abstract matter `T`, no
    `conserv` hypothesis — the matter sector is now concrete and its conservation machine-checked. -/
theorem qiqt_gr_explicit_kg
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
    (hKMS : WedgeKMSFlux_complete g (kgStress m φ g gi) kd hbar)
    (hFocus : ∀ x v, BL (g x) v = 0 → ad x v = BL (fun i j => ricci g gi i j x) v)
    : ∃ Λ : ℝ, ∀ x μ ν, a * kgStress m φ g gi x μ ν = einsteinTensor g gi μ ν x + Λ * g x μ ν := by
  -- `hC`, `hric_symm` and `hreg` are now THEOREMS (Tier A5, A1, A4), supplied internally:
  have hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y) :=
    fun a b c => christoffel_contDiff g gi hCg hCgi a b c
  have hric_symm : ∀ x a' b, ricci g gi a' b x = ricci g gi b a' x :=
    fun x a' b => ricci_symm g gi hsymm hsymm_gi hinv hCg hC a' b x
  have hreg : ∀ f : Point 4 → ℝ,
      (∀ y a' b, a * kgStress m φ g gi y a' b = ricci g gi a' b y + f y * g y a' b) →
      (∀ x ρ, PdiffAt f ρ x) ∧
        Differentiable ℝ (fun y => f y + (1 / 2 : ℝ) * scalarCurv g gi y) :=
    fun f hrel => hreg_kg m φ g gi a hsymm_gi hinv hφ hCg hCgi f hrel
  refine qiqt_gr_from_wedge_kms_complete g gi hsymm hsymm_gi hinv hCg hCgi hC
    (kgStress m φ g gi) η hbar a hbar0 heta ha ?_ hric_symm P Pinv hPP hPP' hcong
    Sf KE A sd kd ad hS hK hA hbound hsat hDnn hD0 hKMS hFocus hreg ?_
  · -- `kgStress` is symmetric (metric symmetry + commuting first derivatives)
    intro x a' b
    simp only [kgStress]
    rw [hsymm x a' b]; ring
  · -- `conserv` discharged internally for the explicit KG field
    intro x ν
    exact kg_conserv_of_contDiff a m φ g gi x ν hsymm hsymm_gi hinv hφ hCg hCgi (hKG x)

/-- **The kinematic-Raychaudhuri form of the explicit-KG QIQT→GR capstone.**  Same as `qiqt_gr_explicit_kg`
    but the labelled focusing input `hFocus` (`ad = R_kk`) is replaced by the *kinematic* Raychaudhuri data of a
    null geodesic congruence (`hgeo`/`hequil`/`harea`) — Jacobson's local-equilibrium setup.  `T = kgStress` is
    concrete and `conserv` is discharged internally, exactly as before. -/
theorem qiqt_gr_explicit_kg_raychaudhuri
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
    (hKMS : WedgeKMSFlux_complete g (kgStress m φ g gi) kd hbar)
    (Vcong : (Fin 4 → ℝ) → Point 4 → Fin 4 → ℝ)
    (hVC : ∀ v μ, ContDiff ℝ ⊤ (fun y => Vcong v y μ))
    (hgeo : ∀ v y μ, ∑ ν, Vcong v y ν * covDerivVec g gi (Vcong v) ν μ y = 0)
    (hVval : ∀ x v, BL (g x) v = 0 → Vcong v x = v)
    (hequil : ∀ x v, BL (g x) v = 0 →
        (∑ μ, ∑ ν, covDerivVec g gi (Vcong v) μ ν x * covDerivVec g gi (Vcong v) ν μ x) = 0)
    (harea : ∀ x v, BL (g x) v = 0 →
        ad x v = - ∑ ν, Vcong v x ν * pd (fun y => expansion g gi (Vcong v) y) ν x)
    (hreg : ∀ f : Point 4 → ℝ,
        (∀ y a' b, a * kgStress m φ g gi y a' b = ricci g gi a' b y + f y * g y a' b) →
        (∀ x ρ, PdiffAt f ρ x) ∧
          Differentiable ℝ (fun y => f y + (1 / 2 : ℝ) * scalarCurv g gi y)) :
    ∃ Λ : ℝ, ∀ x μ ν, a * kgStress m φ g gi x μ ν = einsteinTensor g gi μ ν x + Λ * g x μ ν := by
  have hC : ∀ a b c, ContDiff ℝ ⊤ (fun y => christoffel g gi a b c y) :=
    fun a b c => christoffel_contDiff g gi hCg hCgi a b c
  have hric_symm : ∀ x a' b, ricci g gi a' b x = ricci g gi b a' x :=
    fun x a' b => ricci_symm g gi hsymm hsymm_gi hinv hCg hC a' b x
  refine qiqt_gr_from_wedge_kms_raychaudhuri g gi hsymm hsymm_gi hinv hCg hCgi hC
    (kgStress m φ g gi) η hbar a hbar0 heta ha ?_ hric_symm P Pinv hPP hPP' hcong
    Sf KE A sd kd ad hS hK hA hbound hsat hDnn hD0 hKMS Vcong hVC hgeo hVval hequil harea hreg ?_
  · intro x a' b
    simp only [kgStress]
    rw [hsymm x a' b]; ring
  · intro x ν
    exact kg_conserv_of_contDiff a m φ g gi x ν hsymm hsymm_gi hinv hφ hCg hCgi (hKG x)

end QIQTH.WedgeKMSToGR
