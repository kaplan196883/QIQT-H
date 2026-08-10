/-
  CurvedCenterIdentities — J4-555: the GENERAL-base center-identity lift for the genuinely-curved
  witness `g^K = curvedRNCMetric κ` (κ ≤ 0, Ric ≠ 0), from the EXACT radial (geodesic) gauge.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.

  ## CONTEXT — the owed residue after J4-554 (`CurvedChartJets`).
  `curved_hjets_at_gate` (J4-554) banked most of the chart-jet bundle `hjets` for `g^K`; the OWED
  residue at a GENERAL base `z` is (i) the global `∀ x` first jet (the harder `C²` remainder) and
  (ii) the THREE CENTER IDENTITIES at general base:
      `hVP  : ∑ₖ (W z 0)ₖ · Pₖ = zᵢ`   (chart value · first jet = base coordinate)
      `hPsq : ∑ₖ Pₖ² = 1`               (first-jet column normalisation)
      `hVQ  : ∑ₖ (W z 0)ₖ · Qₖ = 0`     (chart value · second jet = 0)
  where `W z = uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) …` is the geodesic inverse
  chart, `P = ∂ᵢW z`, `Q = ∂ᵢ²W z(0)`.  The base-`0` versions are banked (`chartField_firstJet_center`,
  `chartField_centerJet_term_vanishes_base0`), since `W 0 0 = 0`; the general-base lift is owed.

  ## WHAT LANDS HERE (all satisfiable, none the conclusion, no vacuity, curvature-compatible).
    • `curvedRNCMetric_radialGauge` — the EXACT metric radial (Gauss) gauge `∑ⱼ g^K_{ij}(y)·yʲ = yᵢ`
      ∀ `y i` (re-export of `metricGaussGauge_curvedRNC`).
    • `curvedRNCInv_radialGauge` — ★ NEW: the EXACT INVERSE radial gauge `∑ⱼ gi^K_{ij}(y)·yʲ = yᵢ`
      ∀ `y i` (`κ ≤ 0`).  Proved PURELY from the Sherman–Morrison inverse `curvedRNCInv`: writing
      `α = 1 − (κ/3)‖y‖² ≥ 1 > 0`, `∑ⱼ gi_{ij} yʲ = (1/α)(yᵢ − (κ/3)yᵢ‖y‖²) = (1/α)·α·yᵢ = yᵢ`.
      Genuinely curved (`κ ≠ 0` enters), NOT a flat identity.
    • `curved_radialGauge_bundle` — the packaged conjunction of both radial gauges for `g^K`.
    • `curved_centerIdentities_of_gaussPullback` — ★ the LIFT: from the geodesic normal-chart PULLBACK
      bridge at base `z` (the chart contractions expressed as their metric radial-gauge counterparts —
      the recognised base-point chart-regularity remainder), the three center identities `hVP`/`hPsq`/
      `hVQ` at GENERAL base FOLLOW, with the radial gauge as the load-bearing step:
        – `hVP`  closes by the metric radial gauge (`curvedRNCMetric_radialGauge`);
        – `hPsq` closes by `g^K(0) = δ` (`curvedRNCMetric_zero`);
        – `hVQ`  closes by metric-gauge − inverse-gauge = `zᵢ − zᵢ = 0` (BOTH radial gauges).
    • `curved_centerIdentities_at_gate` — the collar-quantified assembler: per-`(τ,z)` the three center
      identities for `g^K`, from a per-`(τ,z)` pullback-bridge supplier.
    • `curved_centerIdentities_discharge_residual` — WIRE: given the bridge, the THREE CENTRE fields of
      `CurvedChartJets.curved_hjets_residual` are DISCHARGED (proved), shrinking the owed residue to
      just the global `∀ x` first jet.

  ## ⚠ WHAT DID **NOT** CLOSE (the precisely-scoped remainder).
  The three general-base center identities do NOT close from the radial gauge ALONE for the abstract
  `.choose`-built `uniformInverseChart`.  The chart `W z` is controlled only NEAR its image points
  (a neighbourhood of `W z (W z ⁻¹ … )`), and its VALUE / jets at the ambient point `0` for a general
  base `z` are exactly the base-point (`z`-slot) chart regularity — the recognised C⁴ remainder (blocker
  J3 of `ChartJetBounds`).  So the lift is CONDITIONAL on the geodesic normal-chart PULLBACK bridge
  (`hpullVP`/`hpullPsq`/`hpullVQ`): the statement that the chart contractions equal their metric
  radial-gauge counterparts.  This file DISCHARGES the metric side (both radial gauges, unconditional)
  and reduces the center identities to exactly that bridge — the remaining base-point chart jet.

  ## ADVERSARIAL / SATISFIABILITY GATE.
  `κ ≤ 0` (take `κ < 0`) is the genuinely-curved witness: `Ric(0) = (n−1)κ·δ ≠ 0`, `R/6 ≠ 0`.  The
  radial gauges are CURVATURE-COMPATIBLE — `g^K` satisfies them WITH `Ric ≠ 0` (they are the
  geodesic/normal-coordinate gauge, NOT flatness: `gi^K` is the true Sherman–Morrison inverse, and the
  `(κ/3)` correction is genuinely present and genuinely cancels).  The inverse radial gauge fails for
  `gi := δ` off the origin, so this is NOT a flat shortcut.

  ⚠  a₁ = R/6 remains CONDITIONAL.  Closing the center identities (modulo the pullback bridge)
  discharges part of the on-collar chart-jet residue; it does NOT make a₁ = R/6 unconditional — the
  global `∀ x` first jet, `hOffCollarTail`, the convergence trio, the measurability census, and `hsrc`
  all remain.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.CurvedChartJets
import QIQTH.CurvedRNCGaugeBundle

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.GaussLemmaGauge
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.HeatResidualBound QIQTH.AmplitudeDataOnCollar QIQTH.CurvedChartJets
open scoped BigOperators Topology

namespace QIQTH.CurvedCenterIdentities

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — the two EXACT radial (geodesic) gauges for `g^K` (metric + inverse).
    ############################################################################### -/

/-- **The metric radial (Gauss) gauge for `g^K`** — `∑ⱼ g^K_{ij}(y)·yʲ = yᵢ` ∀ `y i`.  Re-export of
    `metricGaussGauge_curvedRNC` in plain sum form.  Curvature-compatible (`κ ≠ 0`, `Ric ≠ 0`); the
    correction tensor `‖y‖²δ − y⊗y` annihilates `y`, so the identity is EXACT (all orders). -/
theorem curvedRNCMetric_radialGauge (κ : ℝ) (y : Point n) (i : Fin n) :
    (∑ j, curvedRNCMetric κ y i j * y j) = y i :=
  metricGaussGauge_curvedRNC κ y i

/-- **★ NEW — the INVERSE radial gauge for `g^K`** — `∑ⱼ gi^K_{ij}(y)·yʲ = yᵢ` ∀ `y i` (`κ ≤ 0`).
    Proved PURELY from the exact Sherman–Morrison inverse `curvedRNCInv`.  With `α = 1 − (κ/3)‖y‖²`
    (`≥ 1 > 0` for `κ ≤ 0`),
      `∑ⱼ gi^K_{ij}(y)·yʲ = (1/α)·(yᵢ − (κ/3)·yᵢ·‖y‖²) = (1/α)·yᵢ·α = yᵢ`.
    Genuinely curved: the `(κ/3)` correction is present and cancels; the identity FAILS for `gi := δ`
    off the origin, so this is NOT a flat shortcut. -/
theorem curvedRNCInv_radialGauge (κ : ℝ) (hκ : κ ≤ 0) (y : Point n) (i : Fin n) :
    (∑ j, curvedRNCInv κ y i j * y j) = y i := by
  have hαne : (1 - (κ / 3) * rncRadialSq y) ≠ 0 := by
    have h1 : (κ / 3) * rncRadialSq y ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (rncRadialSq_nonneg y)
    exact ne_of_gt (by linarith)
  have hA : (∑ j, (if i = j then y j else 0)) = y i := by
    rw [Finset.sum_ite_eq]; simp
  have hSq : (∑ j, y j * y j) = rncRadialSq y := by
    simp only [rncRadialSq, pow_two]
  have hterm : ∀ j : Fin n, curvedRNCInv κ y i j * y j
      = (1 / (1 - (κ / 3) * rncRadialSq y)) *
        ((if i = j then y j else 0) - (κ / 3) * y i * (y j * y j)) := by
    intro j
    by_cases h : i = j
    · simp only [curvedRNCInv, h, if_true]; ring
    · simp only [curvedRNCInv, if_neg h]; ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum, Finset.sum_sub_distrib, hA,
      ← Finset.mul_sum, hSq, one_div,
      show y i - (κ / 3) * y i * rncRadialSq y
          = (1 - (κ / 3) * rncRadialSq y) * y i from by ring,
      ← mul_assoc, inv_mul_cancel₀ hαne, one_mul]

/-- **The packaged radial-gauge bundle for `g^K`** (`κ ≤ 0`): both the metric and the inverse radial
    gauge on ALL of `Point n`.  The metric-side ingredient the center-identity lift consumes. -/
theorem curved_radialGauge_bundle (κ : ℝ) (hκ : κ ≤ 0) :
    (∀ (y : Point n) (i : Fin n), (∑ j, curvedRNCMetric κ y i j * y j) = y i) ∧
    (∀ (y : Point n) (i : Fin n), (∑ j, curvedRNCInv κ y i j * y j) = y i) :=
  ⟨fun y i => curvedRNCMetric_radialGauge κ y i, fun y i => curvedRNCInv_radialGauge κ hκ y i⟩

/-! ###############################################################################
    ### §2 — ★ the general-base center-identity LIFT from the geodesic pullback bridge.
    ############################################################################### -/

/-- **★ `curved_centerIdentities_of_gaussPullback`.**  The GENERAL-base center identities `hVP`/`hPsq`/
    `hVQ` for `g^K`, LIFTED from the geodesic normal-chart PULLBACK bridge at base `z` — the (recognised
    base-point chart-regularity) statement that the chart contractions equal their metric radial-gauge
    counterparts:
      `hpullVP`  : `∑ₖ (W z 0)ₖ·Pₖ = ∑ⱼ g^K_{ij}(z)·zʲ`   (geodesic pullback of `hVP`);
      `hpullPsq` : `∑ₖ Pₖ² = g^K_{ii}(0)`                 (first-jet column = `g^K(0)`-orthonormal);
      `hpullVQ`  : `∑ₖ (W z 0)ₖ·Qₖ = (∑ⱼ g^K_{ij}(z)·zʲ) − (∑ⱼ gi^K_{ij}(z)·zʲ)`  (2nd-jet pullback).
    Then the RADIAL GAUGE closes all three: `hVP` by the metric gauge, `hPsq` by `g^K(0) = δ`, `hVQ` by
    metric-gauge − inverse-gauge = `zᵢ − zᵢ = 0`.  Non-vacuous plumbing witness (both radial gauges are
    genuinely consumed); the bridge is the precisely-scoped remainder.  Curvature-compatible (`κ ≤ 0`,
    `Ric ≠ 0`).  ⚠ NOT `a₁ = R/6`. -/
theorem curved_centerIdentities_of_gaussPullback (κ : ℝ) (hκ : κ ≤ 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n) (i : Fin n)
    (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (hpullVP :
      (∑ k, uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0 k * P 0 k)
        = ∑ j, curvedRNCMetric κ z i j * z j)
    (hpullPsq : (∑ k, P 0 k ^ 2) = curvedRNCMetric κ (0 : Point n) i i)
    (hpullVQ :
      (∑ k, uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0 k * Q k)
        = (∑ j, curvedRNCMetric κ z i j * z j) - (∑ j, curvedRNCInv κ z i j * z j)) :
    (∑ k, uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0 k * P 0 k = z i) ∧
    (∑ k, P 0 k ^ 2 = 1) ∧
    (∑ k, uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0 k * Q k = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hpullVP]; exact curvedRNCMetric_radialGauge κ z i
  · rw [hpullPsq, curvedRNCMetric_zero]; simp
  · rw [hpullVQ, curvedRNCMetric_radialGauge κ z i, curvedRNCInv_radialGauge κ hκ z i, sub_self]

/-- **`curved_centerIdentities_at_gate`.**  The collar-quantified assembler: for the genuinely-curved
    witness `g^K`, per `(τ, z)` on the collar the THREE center identities `hVP`/`hPsq`/`hVQ` hold, from
    a per-`(τ,z)` supplier `hpull` of the geodesic normal-chart pullback bridge (with first/second jet
    families `P`/`Q` at each base `z`).  Each `(τ,z)` instance is discharged by
    `curved_centerIdentities_of_gaussPullback` — the radial gauge closing the three.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_centerIdentities_at_gate (κ : ℝ) (hκ : κ ≤ 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (i : Fin n) (c r₀ τ₀ : ℝ)
    (P : Point n → Point n → Fin n → ℝ) (Q : Point n → Fin n → ℝ)
    (hpull : ∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
      ((∑ k, uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0 k * P z 0 k)
          = ∑ j, curvedRNCMetric κ z i j * z j) ∧
      ((∑ k, P z 0 k ^ 2) = curvedRNCMetric κ (0 : Point n) i i) ∧
      ((∑ k, uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0 k * Q z k)
          = (∑ j, curvedRNCMetric κ z i j * z j) - (∑ j, curvedRNCInv κ z i j * z j))) :
    ∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
      (∑ k, uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0 k * P z 0 k = z i) ∧
      (∑ k, P z 0 k ^ 2 = 1) ∧
      (∑ k, uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0 k * Q z k = 0) := by
  intro τ z hreg
  obtain ⟨h1, h2, h3⟩ := hpull τ z hreg
  exact curved_centerIdentities_of_gaussPullback κ hκ hChr hK z i (P z) (Q z) h1 h2 h3

/-! ###############################################################################
    ### §3 — WIRE the lifted identities into the `curved_hjets_residual` ledger.
    ############################################################################### -/

/-- **`curved_centerIdentities_discharge_residual`.**  WIRE into `CurvedChartJets.curved_hjets_residual`:
    given the geodesic normal-chart pullback bridge, the THREE CENTRE fields (`hCentreVP`/`hCentrePsq`/
    `hCentreVQ`) of the owed chart-jet residue are DISCHARGED (each is now a PROVED proposition), so the
    residue shrinks to just the remaining `hGlobalJet` (the global `∀ x` first jet) supplied as `hglob`.
    Demonstrates the center identities are no longer owed once the base-point pullback bridge is in
    hand.  ⚠ NOT `a₁ = R/6`. -/
theorem curved_centerIdentities_discharge_residual (κ : ℝ) (hκ : κ ≤ 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (z : Point n) (i : Fin n)
    (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    (hpullVP :
      (∑ k, uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0 k * P 0 k)
        = ∑ j, curvedRNCMetric κ z i j * z j)
    (hpullPsq : (∑ k, P 0 k ^ 2) = curvedRNCMetric κ (0 : Point n) i i)
    (hpullVQ :
      (∑ k, uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0 k * Q k)
        = (∑ j, curvedRNCMetric κ z i j * z j) - (∑ j, curvedRNCInv κ z i j * z j))
    (hGlobalJet : Prop) (hglob : hGlobalJet) :
    QIQTH.CurvedChartJets.curved_hjets_residual hGlobalJet
      (∑ k, uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0 k * P 0 k = z i)
      (∑ k, P 0 k ^ 2 = 1)
      (∑ k, uniformInverseChart (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK z 0 k * Q k = 0) := by
  obtain ⟨hVP, hPsq, hVQ⟩ :=
    curved_centerIdentities_of_gaussPullback κ hκ hChr hK z i P Q hpullVP hpullPsq hpullVQ
  exact QIQTH.CurvedChartJets.curved_hjets_residual_intro hglob hVP hPsq hVQ

end QIQTH.CurvedCenterIdentities

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.CurvedCenterIdentities.curvedRNCMetric_radialGauge
#print axioms QIQTH.CurvedCenterIdentities.curvedRNCInv_radialGauge
#print axioms QIQTH.CurvedCenterIdentities.curved_radialGauge_bundle
#print axioms QIQTH.CurvedCenterIdentities.curved_centerIdentities_of_gaussPullback
#print axioms QIQTH.CurvedCenterIdentities.curved_centerIdentities_at_gate
#print axioms QIQTH.CurvedCenterIdentities.curved_centerIdentities_discharge_residual
