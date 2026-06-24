/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# A1+A2 — the concrete (pp-wave) worked example of the QIQT→GR capstone

`qiqt_gr_ppwave` instantiates `qiqt_gr_freefield_complete_covCong` with the **explicit pp-wave metric** and its
**explicit tetrad**: every *geometric* premise (symmetry, inverse, smoothness `hCg`/`hCgi`, the frame
congruence `hcong`, `hPP`/`hPP'`) is discharged concretely for this curved spacetime.

Honestly CONDITIONAL (plan §0): the irreducible FQ/realization inputs (`hbound`/`hcap`/`hK`/`hS`/`hA`), the
matter EOM `hKG` (the curved-background KG field is the documented Stage-4 frontier — carried, not faked), and a
covariantly-constant congruence `W` (per-generator) are carried as hypotheses.  So: **the Einstein equations for
the explicit pp-wave spacetime follow, given the FQ postulate + realization + matter field + congruence** — a
curved-spacetime upgrade of the flat/vacuum `QiqtGrWitness`.

Axiom-free.
-/
import QIQTH.QiqtGrCovCong
import QIQTH.PPWaveMetric

namespace QIQTH.WedgeKMSToGR

open QIQTH.Curvature QIQTH.EinsteinEOS QIQTH.RelEntPositivity QIQTH.BranchLedger
  Complex MeasureTheory Real Filter Topology

/-- **★★★ QIQT→GR for the explicit pp-wave spacetime.**  The Einstein equations
    `a·kgStress = G + Λg` with `g = ppMetric H` (a curved pp-wave), every geometric premise discharged
    concretely (metric/inverse symmetry + `g·gi=I`, smoothness, the explicit tetrad's congruence and
    invertibility).  Carries — honestly, per plan §0 — the matter field + EOM `hKG` (the curved KG field is the
    documented Stage-4 frontier), the FQ/realization inputs (`hbound`/`hcap`/`hK`/`hS`/`hA`), and a
    covariantly-constant congruence `W`.  Axiom-free. -/
theorem qiqt_gr_ppwave
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (H : Point 4 → ℝ) (hCH : ContDiff ℝ ⊤ H)
    (φ : Point 4 → ℝ) (m η hbar a : ℝ)
    (hbar0 : hbar ≠ 0) (hbar_pos : 0 < hbar) (heta : η ≠ 0) (ha : a = 2 * Real.pi / (hbar * η))
    (hφ : ContDiff ℝ ⊤ φ) (hKG : ∀ x, boxField φ (ppMetric H) (ppMetricInv H) x = m ^ 2 * φ x)
    (A : Point 4 → (Fin 4 → ℝ) → ℝ → ℝ) (sd : Point 4 → (Fin 4 → ℝ) → ℝ)
    (pp : Point 4 → (Fin 4 → ℝ) → ℝ → ι → ℝ)
    (hpp_nn : ∀ x v t r, 0 ≤ pp x v t r)
    (hpp1 : ∀ x v t, ∑ r, pp x v t r = 1)
    (hpp0 : ∀ x v, pp x v 0 = (fun _ : ι => (Fintype.card ι : ℝ)⁻¹))
    (hcap : ∀ x v, η * A x v 0 = Real.log (Fintype.card ι))
    (W : Point 4 → (Fin 4 → ℝ) → Point 4 → Fin 4 → ℝ)
    (hWx : ∀ x v, BL (ppMetric H x) v = 0 → W x v x = v)
    (hWC : ∀ x v μ, ContDiff ℝ ⊤ (fun y => W x v y μ))
    (hcov : ∀ x v a b y, covDerivVec (ppMetric H) (ppMetricInv H) (W x v) a b y = 0)
    (hS : ∀ x v, BL (ppMetric H x) v = 0 →
        HasDerivAt (fun t => Shannon Finset.univ (pp x v t)) (sd x v) 0)
    (hK : ∀ x v, BL (ppMetric H x) v = 0 →
        HasDerivAt (fun t => Shannon Finset.univ (pp x v t) + KL Finset.univ (pp x v t) (pp x v 0))
          (2 * Real.pi / hbar * BL (kgStress m φ (ppMetric H) (ppMetricInv H) x) v) 0)
    (hA : ∀ x v, BL (ppMetric H x) v = 0 → HasDerivAt (A x v)
        (- ∑ ν, W x v x ν * pd (fun y => expansion (ppMetric H) (ppMetricInv H) (W x v) y) ν x) 0)
    (hbound : ∀ x v, BL (ppMetric H x) v = 0 →
        ∀ᶠ t in 𝓝 0, Shannon Finset.univ (pp x v t) ≤ η * A x v t)
    (mw : Point 4 → (Fin 4 → ℝ) → ℝ) (hmw : ∀ x v, 0 < mw x v)
    : ∃ Λ : ℝ, ∀ x μ ν,
        a * kgStress m φ (ppMetric H) (ppMetricInv H) x μ ν
          = einsteinTensor (ppMetric H) (ppMetricInv H) μ ν x + Λ * ppMetric H x μ ν :=
  qiqt_gr_freefield_complete_covCong (ι := ι) (ppMetric H) (ppMetricInv H)
    (ppMetric_symm H) (ppMetricInv_symm H) (ppMetric_inv H)
    (ppMetric_contDiff H hCH) (ppMetricInv_contDiff H hCH)
    φ m η hbar a hbar0 hbar_pos heta ha hφ hKG
    (ppFrame H) (ppFrameInv H) (ppFrame_pp H) (ppFrame_pp' H) (ppFrame_cong H)
    A sd pp hpp_nn hpp1 hpp0 hcap W hWx hWC hcov hS hK hA hbound mw hmw

end QIQTH.WedgeKMSToGR
