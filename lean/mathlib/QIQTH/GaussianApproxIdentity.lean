/-
  GaussianApproxIdentity — J4-208: the PLAIN Gaussian approximate identity in the natural
  `𝓝[>] 0` filter form (Sol final plan, Phase 5 — the `hDConv` core building block).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST FIREWALL.  This file is NOT `a₁ = R/6`.  It supplies ONE clean building block of the
  heat-kernel campaign: the plain scalar Gaussian approximate identity
      `∫ z, G_τ(z)·f(z)  →  f(0)`   as `τ ↓ 0`,
  stated over the natural half-open filter `𝓝[>] (0 : ℝ)` (rather than through an arbitrary
  positive null sequence `ε_m ↓ 0`).  It contains NO `sorry`, no new axioms, no `expRho` in
  statements, no vacuous hypotheses, and no conclusion-in-disguise hypothesis.

  ── THE AUDIT (what is already banked vs. what this file adds) ─────────────────────────────────

  Already banked (J4-118 `DeltaFamilyBoundary` + J4-119 `GaussianTailBoundary`):
    • `gaussDdim_integral_eq_one` (M1)        — the `d`-dim Gaussian has TOTAL MASS ONE.
    • `tendsto_integral_gaussDdim_smul` (B1)  — the Lemma-3.14 NEAR/FAR approximate-identity core,
                                                CARRYING the Gaussian tail `hTail` + base meas.
    • `gaussDdim_tail_tendsto_zero` (T1)      — the `hTail` DISCHARGE, UNCONDITIONAL.
    • `tendsto_integral_gaussDdim_smul_of_meas` (T1★)
          — the SCALAR approximate identity with `hTail` GONE, carrying ONLY base measurability,
            but in the SEQUENTIAL shape `Tendsto (fun m => ∫ G_{ε_m}·h) atTop (𝓝 (h 0))` for an
            arbitrary positive null sequence `ε : ℕ → ℝ`.
    • `tendsto_integral_gaussDdim_smul_family` (T2)
          — the equicontinuous-FAMILY sequential identity `∫ G_{ε_m}·h_m → c` under a uniform
            near-origin approach `hEqui`, carrying only base measurability.

  What was MISSING (the gap this file closes): the SAME facts phrased over the honest limiting
  filter `𝓝[>] (0 : ℝ)`, i.e. `Tendsto (fun τ => ∫ z, G_τ(z)·f(z)) (𝓝[>] 0) (𝓝 (f 0))`.  The
  `hDConv` core (Sol Ph5) names exactly this filter form.  Since `𝓝[>] (0 : ℝ)` is countably
  generated, `Filter.tendsto_iff_seq_tendsto` upgrades the banked SEQUENTIAL forms to the filter
  form with no new analysis — the near/far mass argument is entirely reused, not re-proved.

  WHAT LANDS.
    (P1)  `gaussDdim_approx_identity`        — the plain scalar `𝓝[>] 0` approximate identity,
          for `f` bounded, continuous at `0`, a.e.-measurable.  Carries ONLY base measurability,
          exactly like its banked sequential source `tendsto_integral_gaussDdim_smul_of_meas`.
    (P2)  `gaussDdim_approx_identity_family` — the amplitude/family `𝓝[>] 0` version: for a
          time-and-space amplitude `A τ z` uniformly bounded, a.e.-measurable, approaching a
          common value `c` uniformly near the origin (`hEqui`, in `𝓝[>] 0` form), the Gaussian
          sampling converges `∫ z, G_τ(z)·A τ z → c`.  This is the Sol Part-B interface: `hEqui`
          is a genuine equicontinuity/uniform-approach input (NOT the conclusion, non-vacuous),
          matching the banked family lemma's carry.

  NOT `a₁ = R/6`.  One brick.
-/
import Mathlib
import QIQTH.GaussianTailBoundary

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation
open QIQTH.HeatResidualBound
open scoped Topology

namespace QIQTH.GaussianApproxIdentity

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### P1. The plain scalar approximate identity over `𝓝[>] 0`. -/

/-- **★ J4-208 (P1) — THE PLAIN GAUSSIAN APPROXIMATE IDENTITY (`𝓝[>] 0` FORM).**  For
    `f : Point n → ℝ` BOUNDED (`|f z| ≤ C`), CONTINUOUS at `0`, and `volume`-a.e.-measurable,
    the `d`-dimensional Gaussian delta family samples `f` at the origin as the width `τ ↓ 0`:
        `∫ z, gaussDdim τ z · f z  →  f 0`   in `𝓝[>] (0 : ℝ)`.
    ROUTE (no new analysis): `𝓝[>] (0 : ℝ)` is countably generated, so
    `Filter.tendsto_iff_seq_tendsto` reduces the filter statement to its value along every
    positive null sequence `ε_m ↓ 0`, which is the banked, tail-discharged sequential identity
    `tendsto_integral_gaussDdim_smul_of_meas`.  ⚠ CONDITIONAL only on the base measurability
    `hmeas` (deferred measurability family), exactly as the banked source.  NOT `a₁ = R/6`. -/
theorem gaussDdim_approx_identity
    (f : Point n → ℝ) (C : ℝ) (hCbd : ∀ z, |f z| ≤ C)
    (hcont : ContinuousAt f 0) (hmeas : AEStronglyMeasurable f volume) :
    Tendsto (fun τ => ∫ z : Point n, gaussDdim τ z * f z) (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) := by
  rw [Filter.tendsto_iff_seq_tendsto]
  intro ε hε
  exact tendsto_integral_gaussDdim_smul_of_meas ε hε f C hCbd hcont hmeas

/-! ### P2. The amplitude/family approximate identity over `𝓝[>] 0`. -/

/-- **★★ J4-208 (P2) — THE AMPLITUDE/FAMILY APPROXIMATE IDENTITY (`𝓝[>] 0` FORM).**  Let
    `A : ℝ → Point n → ℝ` be a time-and-space amplitude, uniformly bounded (`|A τ z| ≤ C`) and
    (for each `τ`) `volume`-a.e.-measurable.  If `A τ z → c` UNIFORMLY over a shrinking
    origin-neighbourhood as `τ ↓ 0` (`hEqui`: for every `η` there is a ball on which, eventually
    in `𝓝[>] 0`, `|A τ z − c| ≤ η`), then the Gaussian delta family samples the common limit:
        `∫ z, gaussDdim τ z · A τ z  →  c`   in `𝓝[>] (0 : ℝ)`.
    ROUTE: `Filter.tendsto_iff_seq_tendsto` reduces to a positive null sequence `ε_m ↓ 0`, whereon
    it is the banked equicontinuous-family sequential identity
    `tendsto_integral_gaussDdim_smul_family` with `h m := A (ε m)`; the `𝓝[>] 0`-form `hEqui`
    transports to the sequence via `hε.eventually`.  This is the Sol Part-B interface: `hEqui` is a
    genuine uniform-approach (equicontinuity) input — NOT the conclusion, non-vacuous — matching the
    banked family lemma's carry.  ⚠ CONDITIONAL on base measurability `hmeas` and `hEqui`.  NOT
    `a₁ = R/6`. -/
theorem gaussDdim_approx_identity_family
    (A : ℝ → Point n → ℝ) (C : ℝ) (hCbd : ∀ τ z, |A τ z| ≤ C)
    (hmeas : ∀ τ, AEStronglyMeasurable (A τ) volume)
    (c : ℝ)
    (hEqui : ∀ η > 0, ∃ δ > 0, ∀ᶠ τ in 𝓝[>] (0 : ℝ),
        ∀ z ∈ Metric.ball (0 : Point n) δ, |A τ z - c| ≤ η) :
    Tendsto (fun τ => ∫ z : Point n, gaussDdim τ z * A τ z) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  rw [Filter.tendsto_iff_seq_tendsto]
  intro ε hε
  refine tendsto_integral_gaussDdim_smul_family ε hε (fun m => A (ε m)) C
    (fun m z => hCbd (ε m) z) (fun m => hmeas (ε m)) c ?_
  intro η hη
  obtain ⟨δ, hδ, hev⟩ := hEqui η hη
  exact ⟨δ, hδ, hε.eventually hev⟩

/-- **★★ J4-208 (P1 via P2) — SCALAR IDENTITY AS THE `A`-CONSTANT-IN-TIME FAMILY.**  The plain
    scalar identity (P1) is the special case of the family identity (P2) with `A τ z := f z`
    constant in time and `c := f 0`; here `hEqui` follows from `ContinuousAt f 0` alone (the
    approach is uniform because it is `τ`-independent).  Recorded to exhibit P1 and P2 as one
    mechanism; both carry only base measurability.  NOT `a₁ = R/6`. -/
theorem gaussDdim_approx_identity_of_family
    (f : Point n → ℝ) (C : ℝ) (hCbd : ∀ z, |f z| ≤ C)
    (hcont : ContinuousAt f 0) (hmeas : AEStronglyMeasurable f volume) :
    Tendsto (fun τ => ∫ z : Point n, gaussDdim τ z * f z) (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) := by
  refine gaussDdim_approx_identity_family (fun _ => f) C (fun _ z => hCbd z)
    (fun _ => hmeas) (f 0) ?_
  intro η hη
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hcont η hη
  refine ⟨δ, hδ, Filter.Eventually.of_forall (fun τ z hz => ?_)⟩
  have hd : dist (f z) (f 0) < η := hball (by simpa [Metric.mem_ball] using hz)
  rw [Real.dist_eq] at hd
  exact hd.le

end QIQTH.GaussianApproxIdentity

/-! ### Axiom audit. -/

section AxiomChecks

open QIQTH.GaussianApproxIdentity

#print axioms gaussDdim_approx_identity
#print axioms gaussDdim_approx_identity_family
#print axioms gaussDdim_approx_identity_of_family

end AxiomChecks
