/-
  HDConvReducedToRadialGauge — the REDUCTION of `HjetsShape`'s center-identity wall to the clean named
  `RadialNormalCoordinateGauge` interface (the `hDConv` center-identity leg).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.

  ## CONTEXT — the `hDConv` center-identity wall.
  A fresh audit (cp765) found that `hDConv`'s discharge chain
      `HDConvGateThreading.hDConvSlot_AT_GATE` ← `hbnd_concrete` (`DaLimHardTranche`)
        ← `AmplitudeDerivativeData.hD2Hexpand` (`AmplitudePackage`)
        ← `AmpGeometryBundle.HjetsShape`'s center identities `hVP`/`hPsq`/`hVQ`
  bottoms out on a RADIAL / Sherman–Morrison GAUGE property (`∑ⱼ g_{ij}(y)·yʲ = yᵢ`-shaped identities)
  that is TRUE for `curvedRNCMetric κ` but has no ABSTRACT-`g` discharge in the repo, and cannot be
  borrowed from `curvedRNCMetric κ` without colliding with the live capstone's `hframeK` premise (a
  proven vacuity trap, cp466/cp753/cp765).

  ## WHAT THIS FILE LANDS — the reduction, per the campaign's established pattern.
    • `HjetsShape_of_radialGauge` — ★ `HjetsShape g gi hC hK S a b i τ z` FOLLOWS from
      `RadialGaugeInterface.RadialNormalCoordinateGauge g gi` PLUS
        – the geodesic normal-chart PULLBACK bridge at base `z` (`hpullVP`/`hpullPsq`/`hpullVQ`, the
          recognised base-point chart-regularity remainder), and
        – the ALREADY-BANKED mechanical jet suppliers `HjetsShape` needs beyond the center identities
          (`hSopen`/`h0` gate openness+centre, `hV1` global first jet, `hP1` second-jet centre
          `HasDerivAt`, `hA1`/`hA2` amplitude jets) — passed through verbatim.
      The center identities `hVP`/`hPsq`/`hVQ` are supplied by
      `RadialGaugeInterface.abstract_centerIdentities_of_gaussPullback`; the assembly is
      `AmpGeometryBundle.hjets_assemble`.  This replaces the opaque center-identity carry with ONE
      clean named standard-geometry hypothesis (`RadialNormalCoordinateGauge`).
    • `HjetsShape_of_radialGauge_at_gate` — the collar-quantified form: the `∀ τ z, collarRegime → …`
      universal closure, from the collar-quantified pullback supplier + the collar-quantified
      mechanical suppliers.

  ## HOW FAR THIS REACHES (honest scope).  The `HjetsShape` center identities are the DEEPEST leg of
  the `hDConv` chain — the one with no abstract-`g` discharge.  With this reduction, the center-identity
  leg of `hDConv` is now CONDITIONAL on the single clean named `RadialNormalCoordinateGauge` (satisfiable
  by genuinely-curved metrics, `RadialGaugeInterface.radialNormalCoordinateGauge_curved`) plus the
  base-point pullback bridge — NOT on any opaque unnamed wall.  A capstone-level variant swapping
  `hDConv` for `RadialNormalCoordinateGauge` would additionally require reproducing the intervening
  `amplitudeDataOn_concrete` constructor census and the full `hDConvSlot_AT_GATE` ~130-binder census
  (which `HDConvGateThreading` itself declines to restate); that heavy intermediate is NOT materialised
  here.  ⚠ a₁ = R/6 remains CONDITIONAL.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.RadialGaugeInterface

open Finset
open QIQTH.Curvature QIQTH.RadialDistance
open QIQTH.HeatResidualBound QIQTH.AmpGeometryBundle QIQTH.AmplitudeDataOnCollar
open QIQTH.HrepGermFactorization
open QIQTH.RadialGaugeInterface
open scoped BigOperators

namespace QIQTH.HDConvReducedToRadialGauge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### §1 — `HjetsShape` from the named radial gauge + pullback bridge + mechanical jets.
    ############################################################################### -/

/-- **★ `HjetsShape_of_radialGauge`.**  The REDUCTION: `HjetsShape g gi hC hK S a b i τ z` follows from
    `RadialNormalCoordinateGauge g gi` PLUS the geodesic normal-chart pullback bridge at base `z`
    (`hpullVP`/`hpullPsq`/`hpullVQ`) PLUS the already-banked mechanical jet suppliers
    (`hSopen`/`h0`/`hV1`/`hP1`/`hA1`/`hA2`, verbatim the non-center fields of `hjets_assemble`).  The
    three center identities `hVP`/`hPsq`/`hVQ` are produced by
    `abstract_centerIdentities_of_gaussPullback` (the radial gauge closing them); the assembly is
    `hjets_assemble`.  Replaces the opaque center-identity carry with the clean named
    `RadialNormalCoordinateGauge`.  ⚠ NOT `a₁ = R/6`. -/
theorem HjetsShape_of_radialGauge (g gi : Point n → Fin n → Fin n → ℝ)
    (hgauge : RadialNormalCoordinateGauge g gi)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (τ : ℝ) (z : Point n)
    (P : Point n → Fin n → ℝ) (Q : Fin n → ℝ)
    -- mechanical jet suppliers (verbatim the non-center fields of `hjets_assemble`):
    (hSopen : IsOpen (S z)) (h0 : (0 : Point n) ∈ S z)
    (hV1 : ∀ x k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k) (P x k) (x i))
    (hP1 : ∀ k, HasDerivAt
      (fun s : ℝ => P (Function.update (0 : Point n) i s) k) (Q k) ((0 : Point n) i))
    (hA1 : ∀ x, PdiffAt (chartAmp g gi hC hK a b τ z) i x)
    (hA2 : PdiffAt (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i (0 : Point n))
    -- the geodesic normal-chart PULLBACK bridge at base `z`:
    (hpullVP :
      (∑ k, uniformInverseChart g gi hC hK z 0 k * P 0 k) = ∑ j, g z i j * z j)
    (hpullPsq : (∑ k, P 0 k ^ 2) = g (0 : Point n) i i)
    (hpullVQ :
      (∑ k, uniformInverseChart g gi hC hK z 0 k * Q k)
        = (∑ j, g z i j * z j) - (∑ j, gi z i j * z j)) :
    HjetsShape g gi hC hK S a b i τ z := by
  obtain ⟨hVP, hPsq, hVQ⟩ :=
    abstract_centerIdentities_of_gaussPullback g gi hgauge hC hK z i P Q hpullVP hpullPsq hpullVQ
  exact hjets_assemble g gi hC hK S a b i τ z P Q hSopen h0 hV1 hP1 hA1 hA2 hVP hPsq hVQ

/-! ###############################################################################
    ### §2 — the collar-quantified form (`∀ τ z, collarRegime → HjetsShape`).
    ############################################################################### -/

/-- **`HjetsShape_of_radialGauge_at_gate`.**  The collar-quantified reduction: `HjetsShape` for every
    `(τ, z)` in the collar regime, from `RadialNormalCoordinateGauge g gi` + a collar-quantified
    pullback-bridge supplier `hpull` (with per-base first/second jet families `P`/`Q`) + collar-
    quantified mechanical jet suppliers.  Each `(τ,z)` instance is discharged by
    `HjetsShape_of_radialGauge`.  ⚠ NOT `a₁ = R/6`. -/
theorem HjetsShape_of_radialGauge_at_gate (g gi : Point n → Fin n → Fin n → ℝ)
    (hgauge : RadialNormalCoordinateGauge g gi)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (i : Fin n) (c r₀ τ₀ : ℝ)
    (P : Point n → Point n → Fin n → ℝ) (Q : Point n → Fin n → ℝ)
    (hSopen : ∀ z, IsOpen (S z)) (h0 : ∀ z, (0 : Point n) ∈ S z)
    (hV1 : ∀ z x k, HasDerivAt
      (fun s : ℝ => uniformInverseChart g gi hC hK z (Function.update x i s) k) (P z x k) (x i))
    (hP1 : ∀ z k, HasDerivAt
      (fun s : ℝ => P z (Function.update (0 : Point n) i s) k) (Q z k) ((0 : Point n) i))
    (hA1 : ∀ τ z x, PdiffAt (chartAmp g gi hC hK a b τ z) i x)
    (hA2 : ∀ τ z, PdiffAt (fun y => pd (chartAmp g gi hC hK a b τ z) i y) i (0 : Point n))
    (hpull : ∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z →
      ((∑ k, uniformInverseChart g gi hC hK z 0 k * P z 0 k) = ∑ j, g z i j * z j) ∧
      ((∑ k, P z 0 k ^ 2) = g (0 : Point n) i i) ∧
      ((∑ k, uniformInverseChart g gi hC hK z 0 k * Q z k)
          = (∑ j, g z i j * z j) - (∑ j, gi z i j * z j))) :
    ∀ τ z, collarRegime (K := K) r₀ c τ₀ τ z → HjetsShape g gi hC hK S a b i τ z := by
  intro τ z hreg
  obtain ⟨h1, h2, h3⟩ := hpull τ z hreg
  -- pin the base-`z` first/second jet family from the collar-quantified families.
  exact HjetsShape_of_radialGauge g gi hgauge hC hK S a b i τ z
    (P z) (Q z) (hSopen z) (h0 z) (hV1 z) (hP1 z) (hA1 τ z) (hA2 τ z) h1 h2 h3

end QIQTH.HDConvReducedToRadialGauge

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HDConvReducedToRadialGauge.HjetsShape_of_radialGauge
#print axioms QIQTH.HDConvReducedToRadialGauge.HjetsShape_of_radialGauge_at_gate
