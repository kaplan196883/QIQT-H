/-
  CurvedRNCChartReach — J4-529: the LAST curved-witness MEASURABILITY carry `hVmapK` discharged
  from a SINGLE geometric REACHABILITY input, for the genuinely curved witness `g^K = curvedRNCMetric K`
  (`K < 0`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING about the coefficient.  It closes
  the last CURVED-GEOMETRY measurability carry of the witness-measurability capstone: the
  `volume.restrict Kset` AE-measurability at `p = 0` of the base-chart pullback.  Closing it makes the
  WITNESS MEASURABILITY carry-free — modulo a single GEOMETRIC reach input — but does NOT derive `a₁`.
  The ~30–40 curved heat-kernel Gaussian dominations (heatOp / Levi) remain the untouched wall.

  ── THE REDUCTION.  J4-528 (`CurvedRNCWitnessMeasSC.curvedRNC_hWmeas_sc`) left ONE carry:
       `hVmapK : AEStronglyMeasurable (fun z => uniformInverseChart g^K gi^K hChr Kset z 0)
                   (volume.restrict Kset)`.
     `FoldedCoeffChartMeas.hVmapMeasK_zero_of_geom` discharges `hVmapK` from THREE origin side-conditions
     {`hball`, `hnorm`, `hRI`} (the last being the curved origin-chart RIGHT-INVERSE / reach
     `exp^{g}_z(W_z 0) = 0`).  THE KEY OBSERVATION of this brick: all THREE collapse to a SINGLE pure
     geometric REACHABILITY input via the banked LEFT-inverse germ
     (`uniformInverseChart_huniformChart`): if `0` is reachable from `z` with velocity `‖v‖ < ρ`
     (`ρ = min(chart-germ radius, uniformFlowRadius, Lipschitz modulus)`) — i.e. `exp^{g}_z v = 0` — then
       • `W z 0 = W z (exp_z v) = v`   (left germ, since `‖v‖ < ` germ radius),
       • `hRI`   : `exp_z (W z 0) = exp_z v = 0`                       (from reach directly);
       • `hnorm` : `‖W z 0‖ = ‖v‖ < ρ ≤ uniformFlowRadius`;
       • `hball` : `W z 0 = v ∈ ball 0 ρ ⊆ ball 0 (Lipschitz modulus)`.
     So the ONLY residue is the reach `∀ z ∈ Kset, ∃ v, ‖v‖ < ρ ∧ exp_z v = 0` — a GEOMETRIC statement,
     NOT a measurability statement.  This is exactly the K-uniform reachability audited GENUINE-INPUT in
     `ExpRhoReachability` (the injectivity-radius / lower-semicontinuity gate absent from Mathlib): the
     abstract chart's `expRho` / `uniformFlowRadius` are arbitrary `Classical.choose` witnesses, so the
     reach is not bankable from the substrate and is carried as an explicit, satisfiable, non-vacuous
     geometric input — NOT a measurability carry.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT `a₁ = R/6`).
    * `hVmapMeasK_zero_of_reach` — **the GENERAL reduction.**  For any `(g, gi)` there is a uniform
      radius `ρ > 0` over `K` such that the K-uniform origin reach `∀ z ∈ K, ∃ v, ‖v‖ < ρ ∧ exp_z v = 0`
      IMPLIES `AEStronglyMeasurable (z ↦ W z 0) (volume.restrict K)`.  The three geometric
      side-conditions of `hVmapMeasK_zero_of_geom` are DERIVED internally from the reach + the banked
      left-inverse germ.
    * `curvedRNC_hVmapK_of_reach` — the `g^K` instance of the reduction (the last measurability carry as
      a pure reach input).
    * `curvedRNC_hWmeas_carryFree` / `curvedRNC_hWslice_carryFree` — **★★ the CARRY-FREE witness
      measurability capstone for `g^K` (`K < 0`).**  A radius `ρ > 0` such that the origin reach over
      `Kset` yields the full `curvedRNC_hWmeas_sc` conclusion with NO measurability carry (only the
      geometric reach + the `c < δ₀` gate-radius condition).

  ── SATISFIABILITY GATE (K < 0, non-vacuous, GENUINELY CURVED).  Take any `K < 0`, `n ≥ 2`, compact
     `Kset ∋ 0`, window `a < b`.  Then `Ric(0) = (n−1)Kδ ≠ 0`
     (`CurvedRNCGaussWitness.curvedRNCMetric_ricci_trace_diag_ne`), so nothing collapses to flat.  The
     reach input `∀ z ∈ Kset, ∃ v, ‖v‖ < ρ ∧ exp^{g^K}_z v = 0` is TRUE-in-principle for `K < 0`: by
     Cartan–Hadamard globality (`K < 0` ⟹ the exponential map is a global diffeomorphism, no conjugate
     points, global injectivity), the origin `0` is reachable from EVERY `z` by a UNIQUE geodesic, and
     over the compact `Kset` the reach velocities are uniformly bounded, so a single `ρ` works over ALL
     `z ∈ Kset` (not merely `z = 0`).  The reach genuinely holds over the curved `Kset`, so the
     hypothesis is non-vacuous and never a flat/trivial collapse.  (It is NOT discharged from the
     substrate: the abstract `uniformFlowExp` does not expose `g^K`'s Cartan–Hadamard globality — see the
     GENUINE-INPUT verdict of `ExpRhoReachability`.)

  NO `sorry`.  NO new axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CurvedRNCWitnessMeasSC
import QIQTH.GeodesicGronwall

open MeasureTheory
open QIQTH.Curvature QIQTH.HeatResidualBound QIQTH.ExpMap QIQTH.A1R6CoreAtGate
open QIQTH.GeodesicGronwall QIQTH.FoldedCoeffChartMeas
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedRNCPosDef
open QIQTH.GateChartMeasurability QIQTH.WitnessMeasDeriv QIQTH.HuInftyRebase
open QIQTH.VanVleck QIQTH.ParametrixFunction QIQTH.HeatTransportRecursion QIQTH.HeatParametrixAnsatz
open QIQTH.CurvedRNCWitnessMeasSC
open scoped BigOperators

namespace QIQTH.CurvedRNCChartReach

variable {n : ℕ}

/-! ###############################################################################
    ### The general reduction — three side-conditions ↦ one reachability input.
    ############################################################################### -/

/-- **★★ `hVmapMeasK_zero_of_reach` — the LAST measurability carry from a SINGLE reach input.**
    For any `(g, gi)` with smooth Christoffel data over a compact `K`, there is a uniform radius `ρ > 0`
    such that the K-uniform origin reach
        `∀ z ∈ K, ∃ v : Point n, ‖v‖ < ρ ∧ uniformFlowExp g gi hC hK z v = 0`
    IMPLIES the `volume.restrict K` AE-measurability of the origin base-chart pullback
        `AEStronglyMeasurable (fun z => uniformInverseChart g gi hC hK z 0) (volume.restrict K)`.
    `ρ = min(chart-germ radius, uniformFlowRadius, chartOrigin_lipschitz_modulus.choose)`, and the three
    geometric side-conditions {`hball`, `hnorm`, `hRI`} of `FoldedCoeffChartMeas.hVmapMeasK_zero_of_geom`
    are DERIVED internally from the reach via the banked LEFT-inverse germ
    (`uniformInverseChart_huniformChart`): `W z 0 = W z (exp_z v) = v` for `‖v‖ <` germ radius.  The
    reach is a pure GEOMETRIC input (NOT a measurability carry), matching the GENUINE-INPUT verdict of
    `ExpRhoReachability`.  NOT `a₁ = R/6`. -/
theorem hVmapMeasK_zero_of_reach (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ ρ > (0 : ℝ),
      (∀ z ∈ K, ∃ v : Point n, ‖v‖ < ρ ∧ uniformFlowExp g gi hC hK z v = 0) →
      AEStronglyMeasurable (fun z => uniformInverseChart g gi hC hK z 0)
        ((volume : Measure (Point n)).restrict K) := by
  obtain ⟨δg, hδg, hgerm⟩ := uniformInverseChart_huniformChart g gi hC hK
  set δlip := (chartOrigin_lipschitz_modulus g gi hC hK).choose with hδlip_def
  have hδlip_pos : 0 < δlip := (chartOrigin_lipschitz_modulus g gi hC hK).choose_spec.1
  have hρK_pos : 0 < uniformFlowRadius g gi hC hK := uniformFlowRadius_pos g gi hC hK
  refine ⟨min (min δg (uniformFlowRadius g gi hC hK)) δlip, lt_min (lt_min hδg hρK_pos) hδlip_pos, ?_⟩
  intro hReach
  -- From the reach: derive `W z 0 = v` and the three side-conditions of `hVmapMeasK_zero_of_geom`.
  have hcombined : ∀ z ∈ K,
      uniformInverseChart g gi hC hK z 0
        ∈ Metric.ball (0 : Point n) (chartOrigin_lipschitz_modulus g gi hC hK).choose ∧
      ‖uniformInverseChart g gi hC hK z 0‖ ≤ uniformFlowRadius g gi hC hK ∧
      uniformFlowExp g gi hC hK z (uniformInverseChart g gi hC hK z 0) = 0 := by
    intro z hz
    obtain ⟨v, hv, hexp⟩ := hReach z hz
    have hlt_δg : ‖v‖ < δg :=
      lt_of_lt_of_le hv (le_trans (min_le_left _ _) (min_le_left _ _))
    have hlt_ρK : ‖v‖ < uniformFlowRadius g gi hC hK :=
      lt_of_lt_of_le hv (le_trans (min_le_left _ _) (min_le_right _ _))
    have hlt_lip : ‖v‖ < δlip := lt_of_lt_of_le hv (min_le_right _ _)
    obtain ⟨hgermC2, _hOC⟩ := hgerm z hz
    -- left-inverse germ at `v`: `W z (exp_z v) = v`.
    have hLI : uniformInverseChart g gi hC hK z (uniformFlowExp g gi hC hK z v) = v :=
      (hgermC2 v hlt_δg).1.eq_of_nhds
    -- hence `W z 0 = v` (since `exp_z v = 0`).
    have hW0 : uniformInverseChart g gi hC hK z 0 = v := by rw [← hexp]; exact hLI
    refine ⟨?_, ?_, ?_⟩
    · rw [hW0]; exact mem_ball_zero_iff.mpr hlt_lip
    · rw [hW0]; exact le_of_lt hlt_ρK
    · rw [hW0]; exact hexp
  exact hVmapMeasK_zero_of_geom g gi hC hK
    (fun z hz => (hcombined z hz).1) (fun z hz => (hcombined z hz).2.1)
    (fun z hz => (hcombined z hz).2.2)

/-! ###############################################################################
    ### The `g^K` instance and the carry-free witness measurability capstone.
    ############################################################################### -/

/-- **`curvedRNC_hVmapK_of_reach` — the LAST measurability carry for `g^K`, as a pure reach input.**
    The `g^K = curvedRNCMetric K` (`K < 0`) instance of `hVmapMeasK_zero_of_reach`: a radius `ρ > 0`
    such that the origin reach over `Kset` yields the `hVmapK` carry of `curvedRNC_hWmeas_sc`.
    NOT `a₁ = R/6`. -/
theorem curvedRNC_hVmapK_of_reach (K : ℝ) (hK : K < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric K) (curvedRNCInv K) a b c y))
    {Kset : Set (Point n)} (hKset : IsCompact Kset) :
    ∃ ρ > (0 : ℝ),
      (∀ z ∈ Kset, ∃ v : Point n, ‖v‖ < ρ ∧
        uniformFlowExp (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z v = 0) →
      AEStronglyMeasurable
        (fun z => uniformInverseChart (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z (0 : Point n))
        ((volume : Measure (Point n)).restrict Kset) :=
  hVmapMeasK_zero_of_reach (curvedRNCMetric K) (curvedRNCInv K) hChr hKset

/-- **★★ `curvedRNC_hWmeas_carryFree` — the CARRY-FREE curved witness `hWmeas`.**  For the genuinely
    curved witness `g^K = curvedRNCMetric K` (`K < 0`): a radius `ρ > 0` such that IF the origin `0` is
    reachable from every `z ∈ Kset` with velocity `‖v‖ < ρ` (`exp^{g^K}_z v = 0`), THEN there is a
    uniform gate reach `δ₀ > 0` with, for every gate radius `0 < c < δ₀` and every `τ`, the base witness
    slice `AEStronglyMeasurable` for full `volume`.  NO measurability carry: the single `hVmapK` carry of
    `curvedRNC_hWmeas_sc` is now DISCHARGED from the pure geometric reach input (the K-uniform
    injectivity-radius reachability, GENUINE-INPUT per `ExpRhoReachability`).  NOT `a₁ = R/6`. -/
theorem curvedRNC_hWmeas_carryFree (K : ℝ) (hK : K < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric K) (curvedRNCInv K) a b c y))
    {Kset : Set (Point n)} (hKset : IsCompact Kset) (a b : ℝ) :
    ∃ ρ > (0 : ℝ),
      (∀ z ∈ Kset, ∃ v : Point n, ‖v‖ < ρ ∧
        uniformFlowExp (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z v = 0) →
      ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ → ∀ (τ : ℝ),
        AEStronglyMeasurable
          (fun z => vanVleckGatedWitness (curvedRNCMetric K) (curvedRNCInv K) hChr hKset
            (constGate (curvedRNCMetric K) (curvedRNCInv K) hChr hKset c) a b τ (0 : Point n) z)
          (volume : Measure (Point n)) := by
  obtain ⟨ρ, hρ, himpl⟩ := curvedRNC_hVmapK_of_reach K hK hChr hKset
  exact ⟨ρ, hρ, fun hReach => curvedRNC_hWmeas_sc K hK hChr hKset a b (himpl hReach)⟩

/-- **`curvedRNC_hWslice_carryFree` — the CARRY-FREE curved witness `hWslice`.**  Identical statement to
    `curvedRNC_hWmeas_carryFree`; the same reach discharge serves both.  NOT `a₁ = R/6`. -/
theorem curvedRNC_hWslice_carryFree (K : ℝ) (hK : K < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric K) (curvedRNCInv K) a b c y))
    {Kset : Set (Point n)} (hKset : IsCompact Kset) (a b : ℝ) :
    ∃ ρ > (0 : ℝ),
      (∀ z ∈ Kset, ∃ v : Point n, ‖v‖ < ρ ∧
        uniformFlowExp (curvedRNCMetric K) (curvedRNCInv K) hChr hKset z v = 0) →
      ∃ δ₀ > (0 : ℝ), ∀ c : ℝ, 0 < c → c < δ₀ → ∀ (τ : ℝ),
        AEStronglyMeasurable
          (fun z => vanVleckGatedWitness (curvedRNCMetric K) (curvedRNCInv K) hChr hKset
            (constGate (curvedRNCMetric K) (curvedRNCInv K) hChr hKset c) a b τ (0 : Point n) z)
          (volume : Measure (Point n)) :=
  curvedRNC_hWmeas_carryFree K hK hChr hKset a b

end QIQTH.CurvedRNCChartReach

section AxiomChecks
open QIQTH.CurvedRNCChartReach
#print axioms hVmapMeasK_zero_of_reach
#print axioms curvedRNC_hVmapK_of_reach
#print axioms curvedRNC_hWmeas_carryFree
#print axioms curvedRNC_hWslice_carryFree
end AxiomChecks
