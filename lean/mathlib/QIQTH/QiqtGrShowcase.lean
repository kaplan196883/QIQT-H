/-
Copyright (c) 2026 PK. All rights reserved.
Released under Apache 2.0 license.

# The instantiated showcase capstone — QIQT→GR with the floor laid bare

`qiqt_gr_ppwave_showcase` instantiates the pp-wave QIQT→GR capstone (`qiqt_gr_ppwave`) so that **every
geometric and analytic premise is discharged**, leaving as hypotheses **exactly the irreducible physics floor**.
Concretely, on top of the pp-wave geometry already discharged by `qiqt_gr_ppwave`, this theorem additionally
discharges:

* `hA` — the **area derivative** (Raychaudhuri area-rate) — via `area_hasDerivAt_of_covConst`: a covariantly-
  constant (expansion-free) congruence has zero expansion, so the cross-sectional area is constant and its
  derivative is the demanded rate `0` (Workstream B).
* `hbound` — the **entropy bound** `S ≤ η·A` — via `shannon_le_log_card`: with the area set to the holographic
  capacity `c` (`η·c = log|R|`), the Shannon entropy of any record law never exceeds `log|R| = η·c`.

The area is set to the **constant holographic capacity** `c` (expansion-free ⟹ area-preserving), so `hA` and
`hbound` are theorems.

What remains as hypotheses is **exactly the floor** (nothing else):
* `hKG` — the matter **equation of motion** (Klein–Gordon on the pp-wave background);
* `hcap` — the **FQ capacity** identification `η·c = log|R|` (= P4, `Q_R = A/4ℓ_P²`);
* `hS`, `hK` — the **localization map**: the record law `pp` and the requirement that its entropy rate equals
  the stress flux `2π/ℏ·T_kk` (Gap-2). These are *not* dischargeable analytically: at the uniform reference
  `pp 0` the Shannon entropy is stationary (`d/dt Shannon|₀ = 0`, since `∑ p' = 0` and `p₀` is uniform), so the
  *value* of the heat rate is forced to be the stress flux — i.e. the field-coupled record law, the irreducible
  localization input.  Carried honestly, not faked.
* the covariantly-constant congruence `W` (per-generator), and the dimensionful constants.

So this is the cleanest honest statement of **what GR rests on in QIQT-H**: the Einstein equations for the
explicit pp-wave spacetime follow from **EOM + P4 (FQ capacity) + the localization map** — every geometric,
curvature, area-kinematic, and entropy-bound step discharged.  Axiom-free.
-/
import QIQTH.QiqtGrPPWave
import QIQTH.RaychaudhuriCongruence
import QIQTH.RecordContract

namespace QIQTH.WedgeKMSToGR

open QIQTH.Curvature QIQTH.EinsteinEOS QIQTH.RelEntPositivity QIQTH.BranchLedger
  QIQTH.RecordContract Complex MeasureTheory Real Filter Topology

/-- **★★★ The instantiated showcase: QIQT→GR for the explicit pp-wave spacetime, floor laid bare.**  The
    Einstein equations `a·kgStress = G + Λg` with `g = ppMetric H`, with **every geometric and analytic premise
    discharged** — the pp-wave metric/tetrad (via `qiqt_gr_ppwave`), the area derivative `hA` (via
    `area_hasDerivAt_of_covConst`, the expansion-free congruence), and the entropy bound `hbound` (via
    `shannon_le_log_card`, the area = holographic capacity).  The only remaining hypotheses are the irreducible
    floor: the matter EOM `hKG`, the FQ capacity `hcap` (`η·c = log|R|` = P4), and the localization map
    `hS`/`hK` (the field-coupled record law whose entropy rate is the stress flux — Gap-2), plus the
    covariantly-constant congruence and constants.  Axiom-free. -/
theorem qiqt_gr_ppwave_showcase
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (H : Point 4 → ℝ) (hCH : ContDiff ℝ ⊤ H)
    (φ : Point 4 → ℝ) (m η hbar a : ℝ)
    (hbar0 : hbar ≠ 0) (hbar_pos : 0 < hbar) (heta : η ≠ 0) (ha : a = 2 * Real.pi / (hbar * η))
    (hφ : ContDiff ℝ ⊤ φ) (hKG : ∀ x, boxField φ (ppMetric H) (ppMetricInv H) x = m ^ 2 * φ x)
    -- P4 — the FQ holographic capacity: the area saturates the record capacity `log|R|/η` (carried):
    (c : ℝ) (hcap : η * c = Real.log (Fintype.card ι))
    -- the localization map (carried): the record law `pp`, and `hS`/`hK` coupling its entropy rate to T_kk:
    (sd : Point 4 → (Fin 4 → ℝ) → ℝ)
    (pp : Point 4 → (Fin 4 → ℝ) → ℝ → ι → ℝ)
    (hpp_nn : ∀ x v t r, 0 ≤ pp x v t r)
    (hpp1 : ∀ x v t, ∑ r, pp x v t r = 1)
    (hpp0 : ∀ x v, pp x v 0 = (fun _ : ι => (Fintype.card ι : ℝ)⁻¹))
    (W : Point 4 → (Fin 4 → ℝ) → Point 4 → Fin 4 → ℝ)
    (hWx : ∀ x v, BL (ppMetric H x) v = 0 → W x v x = v)
    (hWC : ∀ x v μ, ContDiff ℝ ⊤ (fun y => W x v y μ))
    (hcov : ∀ x v p q y, covDerivVec (ppMetric H) (ppMetricInv H) (W x v) p q y = 0)
    (hS : ∀ x v, BL (ppMetric H x) v = 0 →
        HasDerivAt (fun t => Shannon Finset.univ (pp x v t)) (sd x v) 0)
    (hK : ∀ x v, BL (ppMetric H x) v = 0 →
        HasDerivAt (fun t => Shannon Finset.univ (pp x v t) + KL Finset.univ (pp x v t) (pp x v 0))
          (2 * Real.pi / hbar * BL (kgStress m φ (ppMetric H) (ppMetricInv H) x) v) 0)
    (mw : Point 4 → (Fin 4 → ℝ) → ℝ) (hmw : ∀ x v, 0 < mw x v)
    : ∃ Λ : ℝ, ∀ x μ ν,
        a * kgStress m φ (ppMetric H) (ppMetricInv H) x μ ν
          = einsteinTensor (ppMetric H) (ppMetricInv H) μ ν x + Λ * ppMetric H x μ ν :=
  qiqt_gr_ppwave H hCH φ m η hbar a hbar0 hbar_pos heta ha hφ hKG
    (fun _ _ _ => c) sd pp hpp_nn hpp1 hpp0
    (fun _ _ => hcap)
    W hWx hWC hcov hS hK
    -- hA: the constant area (expansion-free congruence) has the Raychaudhuri area-rate as derivative:
    (fun x v _ => area_hasDerivAt_of_covConst (ppMetric H) (ppMetricInv H) (W x v)
      (fun p q y => hcov x v p q y) x c)
    -- hbound: Shannon(pp t) ≤ log|R| = η·c (the holographic capacity), for every t:
    (fun x v _ => Filter.Eventually.of_forall (fun t => by
      show Shannon Finset.univ (pp x v t) ≤ η * c
      rw [hcap]; exact shannon_le_log_card (pp x v t) (hpp_nn x v t) (hpp1 x v t)))
    mw hmw

end QIQTH.WedgeKMSToGR
