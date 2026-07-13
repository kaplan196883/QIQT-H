/-
  HEAT-COEFFICIENT → CORRESPONDENCE BRIDGE — relocating the `a₁ = R/6` assumption to its honest
  minimum (heat-kernel gap plan, Phase-5 wiring).

  `SeeleyDeWittInterface` carried `a₁ = R/6 + tr E` as a bare field.  This file REPLACES that stipulation
  by SOURCING it from `HeatCoeffDetermination`: the `a₁` identity is now DERIVED (`coeff2_eq`) from
  Gilkey's invariance ansatz + the flat/curved model evaluations.  The whole correspondence then carries
  only the weaker (invariance + model) assumptions instead of the specific number.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  MANDATORY FIREWALL (binding, honest — read this before concluding anything is "assumption-free").

  This is a RELOCATION, NOT a removal.  The assumptions are NOT gone; they are moved to their honest,
  more-fundamental minimum:
    • CARRIED, irreducibly (the heat-expansion analytic wall, `HeatCoeffData`'s fields — never axioms):
      (i) Gilkey's UNIVERSALITY ansatz `∃ cTau cE, ∀ P, a₂ P = cTau·τ P + cE·trE P` (Weyl invariant
          theory for O(m) — not in Mathlib);
      (ii) the flat constant-`E` model heat value `(τ,trE,a₂) = (0,1,1)`;
      (iii) the curved `E=0` model heat value `(τ,trE,a₂) = (T,0,T/6)` — this is where the number `1/6`
            still enters, as one geometry's carried heat coefficient.
    • DERIVED: `cTau = 1/6`, `cE = 1`, and `a₂ = τ/6 + trE` universally — hence the `SeeleyDeWittData`
      `a₁` identity, hence the correspondence, WITHOUT a bare `a₁ = R/6` stipulation.
  The residue (i)+(ii)+(iii) is exactly Gilkey Thm 4.8.16 — the heat-trace short-time expansion — which
  can only be DERIVED (not carried) by building the heat semigroup + kernel + Seeley–DeWitt expansion
  (Phases 3–4), the deep wall absent from every proof assistant.  It is NOT removed here and CANNOT be
  removed without that wall or an axiom (this file adds neither).  The correspondence remains CONDITIONAL;
  NOT a proof of the conjecture, NOT the strong holographic principle, NOT quantum gravity.  No axioms,
  no `sorry`.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HeatCoeffDetermination
import QIQTH.SeeleyDeWittInterface

namespace QIQTH.HeatCoeffBridge

open QIQTH.HeatCoeffDetermination QIQTH.SeeleyDeWittInterface QIQTH.CorrespondenceAssembly
open QIQTH.ConicalSakharov QIQTH.Conjectures

variable {ι : Type*}

/-- **The Seeley–DeWitt interface data built FROM a `HeatCoeffData` at index `P`.**  The `a₁` identity
    field is now DERIVED from `HeatCoeffData.coeff2_eq` (Gilkey universality + model evals), not carried
    as a bare stipulation. -/
def seeleyDeWittOfHeatCoeff (D : HeatCoeffData ι) (P : ι) : SeeleyDeWittData where
  R := D.tau P
  trE := D.trE P
  a0 := 1
  a1 := D.heatCoeff2 P
  a0_eq := rfl
  a1_eq := by simp only [a1Laplace]; exact D.coeff2_eq P

@[simp] theorem seeleyDeWittOfHeatCoeff_a1 (D : HeatCoeffData ι) (P : ι) :
    (seeleyDeWittOfHeatCoeff D P).a1 = D.heatCoeff2 P := rfl

@[simp] theorem seeleyDeWittOfHeatCoeff_R (D : HeatCoeffData ι) (P : ι) :
    (seeleyDeWittOfHeatCoeff D P).R = D.tau P := rfl

@[simp] theorem seeleyDeWittOfHeatCoeff_trE (D : HeatCoeffData ι) (P : ι) :
    (seeleyDeWittOfHeatCoeff D P).trE = D.trE P := rfl

/-- **★ THE CORRESPONDENCE with the `a₁` input sourced from the heat-coefficient DETERMINATION.**  Given
    a `HeatCoeffData` and a minimal-scalar index `P` (`trE P = 0`) matched to the region's curvature, and
    the carried cutoff/regulator inputs (#4/#5), the constructed continuum data satisfies the conjecture
    — with the curvature-side assumption now the weaker Gilkey invariance ansatz + model evaluations,
    NOT a bare `a₁ = R/6`. -/
theorem flatSpaceCorrespondence_of_heatCoeff (D : HeatCoeffData ι) (P : ι) (hE0 : D.trE P = 0)
    (DC : ConstructiveCLD)
    (hR : D.tau P = DC.curvR) (ha1 : D.heatCoeff2 P = DC.a1coeff)
    (h5 : ∀ R, DC.recEnt R = Sent DC.N (DC.areaOf R) DC.entReg)
    (h4 : DC.newtonReg = DC.entReg)
    (hnm : DC.sakInvG = dInvG DC.N DC.entReg)
    (hne : dInvG DC.N DC.entReg ≠ 0) :
    FlatSpaceRecordGravityCorrespondence DC.toOpaque :=
  flatSpaceCorrespondence_of_seeleyDeWitt DC (seeleyDeWittOfHeatCoeff D P) hR hE0 ha1 h5 h4 hnm hne

end QIQTH.HeatCoeffBridge
