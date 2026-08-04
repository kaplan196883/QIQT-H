/-
  InftyRebaseCapstone — J4-182: the `⊤ ↦ ∞` interface-rebase capstone.  ONE brick of the a₁ = R/6
  heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING about `R/6`.  It is a pure
  regularity-plumbing capstone: it demonstrates the PURPOSE of the `⊤ ↦ ∞` interface rebase of
  `SpatialC2.hCH_discharge` (J4-182), by feeding the witness-diagonal spatial-`C²` slot END-TO-END
  from the `C^∞` geometry `{hg, hgi, hgpos}` ALONE — with NO transport-coefficient smoothness `hu`
  carry anywhere (the analytic `ω = ⊤` level is never touched).  No conclusion-in-disguise; no
  vacuous / unsatisfiable hypotheses; NO `sorry`; NO new axioms.

  ── THE REBASE (recap).  J4-175 (`HuInftyRebase.hu_infty_closed`) closed the transport-coefficient
     carry at `C^∞` (`∞`) from `{hg, hgi, hgpos}`, the honest level replacing the unreachable analytic
     (`ω = ⊤`) solve.  J4-182 rebased `SpatialC2.hCH_discharge`'s `hu` hypothesis `⊤ ↦ ∞` in place
     (its proof only downcasts `hu` to `C²` via `.of_le`, so the rebase is a pure interface edit).
     This file WIRES the two together.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms).

    • `hCH_discharge_from_geometry` — ★★ the `hCH` (spatial-`C²` witness-diagonal) slot delivered from
        `{hg, hgi, hgpos}` (+ the geometric gate/chart carries `hK0, hS0, hSopen, hg0, hChr`) ALONE:
        `hu_infty_closed` closes the coefficient carry at `∞`, which now feeds the rebased
        `hCH_discharge` DIRECTLY (no `⊤` `hu`).
    • `hsrc_from_geometry` — the `∞`-level transport-source smoothness
        `ContDiff ℝ ∞ (transportOp (vanVleck g) g gi (transportCoeff … 0))` from `{hg, hgi, hgpos}`
        via `transportOp_preserves_contDiff_infty` applied to `u₀`.  This is the HONEST (`∞`) form of
        the `hsrc` carry of `SpatialC2.a1_R6_of_residue_hCH_discharged` — geometry-derivable at the
        finite `C^∞` level.

  ── WHAT REMAINS CARRIED (each satisfiable, non-vacuous, NEVER the conclusion).
    • `{hg, hgi, hgpos}` — the `C^∞` metric / inverse-metric components and `det g > 0` (the campaign's
      genuine geometric inputs).
    • the gate/chart geometry `{hK0, hS0, hSopen, hg0, hChr}` — pure chart geometry at the centre.
    • ⚠ THE `⊤` `hsrc` WALL.  `SpatialC2.a1_R6_of_residue_hCH_discharged` still consumes `hsrc` at the
      ANALYTIC level `⊤` (it feeds `CapstoneStatus.a1_R6_of_residue`, whose own `hsrc` is `⊤`).  That
      is the UNIVERSAL analytic-solve wall (J4-174), NOT rebased here — `hsrc_from_geometry` supplies
      only the honest `∞` form.  The `hu` slot of `a1_R6_of_residue_hCH_discharged`, by contrast, feeds
      ONLY the rebased `hCH_discharge`, so it IS now geometry-derivable at `∞`.

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.SpatialC2
import QIQTH.HuInftyRebase

open MeasureTheory
open QIQTH.Curvature QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.HeatResidualBound QIQTH.HuInftyRebase
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.InftyRebaseCapstone

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-- **★★ `hCH_discharge_from_geometry` — the `hCH` slot from `{hg, hgi, hgpos}` alone.**  The spatial-
    `C²` of the concrete `N = 1` gated van-Vleck witness diagonal slice,
      `ContDiffAt ℝ 2 (fun p ↦ vanVleckGatedWitness g gi hChr hK S a b t p 0) 0`,
    fed END-TO-END from the `C^∞` geometry: `HuInftyRebase.hu_infty_closed` closes the transport-
    coefficient carry at `∞` from `{hg, hgi, hgpos}`, and the J4-182–rebased `SpatialC2.hCH_discharge`
    (whose `hu` hypothesis is now at `∞`, not the unreachable analytic `⊤`) consumes it DIRECTLY.  No
    `hu` carry survives — the transport-coefficient smoothness vanishes into `{hg, hgi, hgpos}`.  The
    remaining carries `{hChr, hK0, hS0, hSopen, hg0}` are the gate/chart geometry at the centre.
    NOT `a₁ = R/6`. -/
theorem hCH_discharge_from_geometry (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t : ℝ) (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0) (hSopen : IsOpen (S 0))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j) :
    ContDiffAt ℝ 2 (fun p => vanVleckGatedWitness g gi hChr hK S a b t p 0) (0 : Point n) :=
  hCH_discharge g gi hChr hK S a b t hK0 hS0 hSopen hg hg0
    (hu_infty_closed g gi hg hgi hgpos)

/-- **`hsrc_from_geometry` — the transport-source smoothness at the honest `∞` level.**  From
    `{hg, hgi, hgpos}` alone,
      `ContDiff ℝ ∞ (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0))`,
    via `HuInftyRebase.transportOp_preserves_contDiff_infty` applied to the `∞`-smooth `0`-th transport
    coefficient `u₀` (`hu_infty_closed … 0`).  This is the `C^∞` form of the `hsrc` carry of
    `SpatialC2.a1_R6_of_residue_hCH_discharged`; the `⊤` (analytic) form that `a1_R6_of_residue`
    consumes is the universal analytic-solve wall, NOT reachable from geometry.  NOT `a₁ = R/6`. -/
theorem hsrc_from_geometry (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v)) :
    ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)) :=
  transportOp_preserves_contDiff_infty g gi hg hgi hgpos
    (transportCoeff (transportOp (vanVleck g) g gi) 0)
    (hu_infty_closed g gi hg hgi hgpos 0)

end QIQTH.InftyRebaseCapstone

section AxiomChecks
open QIQTH.InftyRebaseCapstone
#print axioms hCH_discharge_from_geometry
#print axioms hsrc_from_geometry
end AxiomChecks
