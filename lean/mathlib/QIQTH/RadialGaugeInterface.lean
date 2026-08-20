/-
  RadialGaugeInterface — the clean NAMED geometric hypothesis for the `hDConv` center-identity wall.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It converts
  ONE opaque analytic wall — the general-base center identities `hVP`/`hPsq`/`hVQ` that
  `AmpGeometryBundle.HjetsShape` consumes (and which propagate up `hD2Hexpand → hbnd_concrete →
  hDConvSlot_AT_GATE → hDConv`) — into ONE clean, precisely-named, STANDARD geometric hypothesis:
  `RadialNormalCoordinateGauge`, the Gauss-lemma / radial-gauge property of Riemannian normal
  coordinates.  Following the campaign's established pattern (`JointSecondOrderRNCRegularity`,
  `VanVleckGatedSpatialSymmetry`, `MixedDirectionsFieldHessianEnvelope` for `hCConv`): name the wall,
  then prove the REDUCTION.

  ## THE INTERFACE.
  `RadialNormalCoordinateGauge g gi` bundles the three STANDARD textbook facts of Riemannian normal
  coordinates about ANY metric `g` and its inverse `gi`:
    (1) `metricGauge`  — the metric radial (Gauss) gauge  `∑ⱼ g_{ij}(y)·yʲ = yᵢ`  ∀ `y i`;
    (2) `invGauge`     — the inverse radial gauge          `∑ⱼ gi_{ij}(y)·yʲ = yᵢ`  ∀ `y i`;
    (3) `centerNorm`   — the centre normalisation          `g_{ii}(0) = 1`  ∀ `i`  (`g(0) = δ` diagonal).
  These are EXACTLY the metric-side ingredients the `CurvedCenterIdentities` lift consumes; here they
  are stated GENERICALLY (abstract `g gi`), NOT tied to `curvedRNCMetric κ`.

  ## NON-VACUITY / CURVATURE-COMPATIBILITY (the load-bearing adversarial gate).
    • `radialNormalCoordinateGauge_flat`   — the flat metric `δ` satisfies it (trivial satisfiability);
    • `radialNormalCoordinateGauge_curved` — ★ the GENUINELY CURVED witness `g^K = curvedRNCMetric κ`
      (`κ ≤ 0`, `Ric(0) = (n−1)κ·δ ≠ 0`, `R/6 ≠ 0`) satisfies it, via `curved_radialGauge_bundle` +
      `curvedRNCMetric_zero`.  So the hypothesis is NOT a flatness shortcut and does NOT collapse
      curvature (it is CURVATURE-COMPATIBLE): it is satisfied WITH `Ric ≠ 0`.  This is the exact
      cp466/cp753/cp765 vacuity-trap check — the inverse radial gauge genuinely uses the `(κ/3)`
      Sherman–Morrison correction, which is present and cancels; it FAILS for `gi := δ` off the origin.

  ## THE REDUCTION (this file).
  `abstract_centerIdentities_of_gaussPullback` — the ABSTRACT analog of
  `CurvedCenterIdentities.curved_centerIdentities_of_gaussPullback`: from the geodesic normal-chart
  PULLBACK bridge at base `z` (the recognised base-point chart-regularity remainder) PLUS
  `RadialNormalCoordinateGauge g gi`, the three center identities `hVP`/`hPsq`/`hVQ` FOLLOW at GENERAL
  base — the radial gauge closing all three exactly as in the curved file.

  ⚠  a₁ = R/6 remains CONDITIONAL.  This file replaces one opaque carry (`hDConv`'s center identities)
  with one clean named standard-geometry hypothesis; it does NOT make `a₁ = R/6` unconditional.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.AmpGeometryBundle
import QIQTH.CurvedCenterIdentities

open Finset
open QIQTH.Curvature QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedCenterIdentities
open scoped BigOperators

namespace QIQTH.RadialGaugeInterface

variable {n : ℕ}

/-! ###############################################################################
    ### §1 — the clean NAMED interface: the Riemannian radial (Gauss) gauge.
    ############################################################################### -/

/-- **★ `RadialNormalCoordinateGauge`.**  The clean, precisely-named geometric hypothesis that
    isolates the general-base center-identity wall of `HjetsShape`.  It bundles the three STANDARD
    facts of Riemannian normal coordinates about an abstract metric `g` and its inverse `gi`:
      • `metricGauge` — the metric radial (Gauss) gauge  `∑ⱼ g_{ij}(y)·yʲ = yᵢ`;
      • `invGauge`    — the inverse radial gauge          `∑ⱼ gi_{ij}(y)·yʲ = yᵢ`;
      • `centerNorm`  — the centre normalisation          `g_{ii}(0) = 1`  (`g(0) = δ` diagonal).
    Genuinely satisfiable by CURVED metrics (`radialNormalCoordinateGauge_curved`), NOT a flat
    shortcut.  ⚠ NOT `a₁ = R/6`. -/
structure RadialNormalCoordinateGauge (g gi : Point n → Fin n → Fin n → ℝ) : Prop where
  /-- The metric radial (Gauss) gauge: `∑ⱼ g_{ij}(y)·yʲ = yᵢ` for all `y i`. -/
  metricGauge : ∀ (y : Point n) (i : Fin n), (∑ j, g y i j * y j) = y i
  /-- The inverse radial gauge: `∑ⱼ gi_{ij}(y)·yʲ = yᵢ` for all `y i`. -/
  invGauge : ∀ (y : Point n) (i : Fin n), (∑ j, gi y i j * y j) = y i
  /-- The centre normalisation: `g_{ii}(0) = 1` for all `i` (the `g(0) = δ` diagonal). -/
  centerNorm : ∀ i : Fin n, g (0 : Point n) i i = 1

/-! ###############################################################################
    ### §2 — NON-VACUITY: flat AND genuinely-curved witnesses.
    ############################################################################### -/

/-- **`radialNormalCoordinateGauge_flat`.**  Trivial satisfiability: the flat metric `δ_{ij}` (with
    inverse `δ_{ij}`) satisfies `RadialNormalCoordinateGauge`.  Both radial gauges reduce to
    `∑ⱼ δ_{ij}·yʲ = yᵢ`, the centre normalisation to `δ_{ii} = 1`.  ⚠ NOT `a₁ = R/6`. -/
theorem radialNormalCoordinateGauge_flat :
    RadialNormalCoordinateGauge
      (fun (_ : Point n) i j => if i = j then (1 : ℝ) else 0)
      (fun (_ : Point n) i j => if i = j then (1 : ℝ) else 0) where
  metricGauge y i := by
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  invGauge y i := by
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  centerNorm i := by simp

/-- **★ `radialNormalCoordinateGauge_curved`.**  THE LOAD-BEARING NON-VACUITY WITNESS: the genuinely
    CURVED metric `g^K = curvedRNCMetric κ` (`κ ≤ 0`, so `Ric(0) = (n−1)κ·δ ≠ 0` and `R/6 ≠ 0`) with
    its exact Sherman–Morrison inverse `curvedRNCInv κ` satisfies `RadialNormalCoordinateGauge`.
    Proof: `curved_radialGauge_bundle` (both radial gauges, the inverse one genuinely using the
    `(κ/3)` correction) + `curvedRNCMetric_zero` (centre `= δ`).  Curvature-compatible: the hypothesis
    does NOT force flatness / curvature collapse (cf. cp466/cp753/cp765 vacuity trap).  ⚠ NOT `a₁ = R/6`. -/
theorem radialNormalCoordinateGauge_curved (κ : ℝ) (hκ : κ ≤ 0) :
    RadialNormalCoordinateGauge (curvedRNCMetric (n := n) κ) (curvedRNCInv (n := n) κ) where
  metricGauge y i := (curved_radialGauge_bundle κ hκ).1 y i
  invGauge y i := (curved_radialGauge_bundle κ hκ).2 y i
  centerNorm i := by rw [curvedRNCMetric_zero]; simp

/-! ###############################################################################
    ### §3 — the ABSTRACT center-identity LIFT from the pullback bridge.
    ############################################################################### -/

/-- **★ `abstract_centerIdentities_of_gaussPullback`.**  The ABSTRACT analog of
    `CurvedCenterIdentities.curved_centerIdentities_of_gaussPullback`.  From the geodesic normal-chart
    PULLBACK bridge at base `z` — the (recognised base-point chart-regularity) statements that the
    chart contractions equal their metric radial-gauge counterparts:
      `hpullVP`  : `∑ₖ (W z 0)ₖ·Pₖ = ∑ⱼ g_{ij}(z)·zʲ`;
      `hpullPsq` : `∑ₖ Pₖ² = g_{ii}(0)`;
      `hpullVQ`  : `∑ₖ (W z 0)ₖ·Qₖ = (∑ⱼ g_{ij}(z)·zʲ) − (∑ⱼ gi_{ij}(z)·zʲ)`
    — PLUS `RadialNormalCoordinateGauge g gi`, the three center identities `hVP`/`hPsq`/`hVQ` follow at
    GENERAL base: `hVP` by the metric gauge, `hPsq` by `g(0)=δ`, `hVQ` by metric-gauge − inverse-gauge
    `= zᵢ − zᵢ = 0`.  Non-vacuous plumbing (both radial gauges genuinely consumed); the bridge is the
    precisely-scoped remainder.  ⚠ NOT `a₁ = R/6`. -/
theorem abstract_centerIdentities_of_gaussPullback (g gi : Point n → Fin n → Fin n → ℝ)
    (hgauge : RadialNormalCoordinateGauge g gi)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n) (i : Fin n)
    (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (hpullVP :
      (∑ k, uniformInverseChart g gi hC hK z 0 k * P 0 k) = ∑ j, g z i j * z j)
    (hpullPsq : (∑ k, P 0 k ^ 2) = g (0 : Point n) i i)
    (hpullVQ :
      (∑ k, uniformInverseChart g gi hC hK z 0 k * Q k)
        = (∑ j, g z i j * z j) - (∑ j, gi z i j * z j)) :
    (∑ k, uniformInverseChart g gi hC hK z 0 k * P 0 k = z i) ∧
    (∑ k, P 0 k ^ 2 = 1) ∧
    (∑ k, uniformInverseChart g gi hC hK z 0 k * Q k = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hpullVP]; exact hgauge.metricGauge z i
  · rw [hpullPsq]; exact hgauge.centerNorm i
  · rw [hpullVQ, hgauge.metricGauge z i, hgauge.invGauge z i, sub_self]

/-- **`abstract_centerIdentities_at_gate`.**  The collar-quantified assembler (abstract analog of
    `curved_centerIdentities_at_gate`): per `(τ, z)` on the collar, the three center identities from a
    per-`(τ,z)` supplier of the geodesic normal-chart pullback bridge, closed by the radial gauge.
    ⚠ NOT `a₁ = R/6`. -/
theorem abstract_centerIdentities_at_gate (g gi : Point n → Fin n → Fin n → ℝ)
    (hgauge : RadialNormalCoordinateGauge g gi)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (i : Fin n) (c r₀ τ₀ : ℝ)
    (P : Point n → Point n → Fin n → ℝ) (Q : Point n → Fin n → ℝ)
    (hpull : ∀ τ z, QIQTH.AmplitudeDataOnCollar.collarRegime (K := K) r₀ c τ₀ τ z →
      ((∑ k, uniformInverseChart g gi hC hK z 0 k * P z 0 k) = ∑ j, g z i j * z j) ∧
      ((∑ k, P z 0 k ^ 2) = g (0 : Point n) i i) ∧
      ((∑ k, uniformInverseChart g gi hC hK z 0 k * Q z k)
          = (∑ j, g z i j * z j) - (∑ j, gi z i j * z j))) :
    ∀ τ z, QIQTH.AmplitudeDataOnCollar.collarRegime (K := K) r₀ c τ₀ τ z →
      (∑ k, uniformInverseChart g gi hC hK z 0 k * P z 0 k = z i) ∧
      (∑ k, P z 0 k ^ 2 = 1) ∧
      (∑ k, uniformInverseChart g gi hC hK z 0 k * Q z k = 0) := by
  intro τ z hreg
  obtain ⟨h1, h2, h3⟩ := hpull τ z hreg
  exact abstract_centerIdentities_of_gaussPullback g gi hgauge hC hK z i (P z) (Q z) h1 h2 h3

end QIQTH.RadialGaugeInterface

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.RadialGaugeInterface.radialNormalCoordinateGauge_flat
#print axioms QIQTH.RadialGaugeInterface.radialNormalCoordinateGauge_curved
#print axioms QIQTH.RadialGaugeInterface.abstract_centerIdentities_of_gaussPullback
#print axioms QIQTH.RadialGaugeInterface.abstract_centerIdentities_at_gate
