/-
  InterfaceArrowCensus — J4-264: the inner-interface arrow census + discharge on top of the wide
  `a₁` residual capstone `WideA1AssemblyTrunc.wide_a1_R6_both_slots_internal` (J4-263).  ONE brick of
  the `a₁ = R/6` heat-kernel campaign.  NOT `a₁ = R/6`; proves NOTHING new about `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  This file carries NO coefficient/geometry content of its own.  It (1) audits the
  honest remaining carries of `wide_a1_R6_both_slots_internal` — the six inner interface-arrow
  antecedents `hS0/hDuhamel/hInter/hDConv/hCH/hCConv` and the S1 `∀`-gate `hEmeas` — against the banked
  narrow-route provider bank, and (2) DISCHARGES exactly the two arrows that have a fully-geometric
  banked provider (`hS0`, `hCH`), producing the shorter capstone `wide_a1_R6_interface_discharged`.  It
  does NOT close `a₁ = R/6`; the surviving inner interface `{hDuhamel, hInter, hDConv, hCConv}` and the
  S1 `∀`-gate remain genuine carries.

  ── STRUCTURAL FACT that gates the whole census.  In `wide_a1_R6_both_slots_internal` the gate
     `(a,b,S)` is PROVIDER-CHOSEN (existential in the conclusion `∃ a b C' S, …`).  The six arrows are
     the ANTECEDENTS of the returned implication and reference that hidden `S`.  A banked provider can
     therefore discharge an antecedent only if it supplies the fact for the SAME `S` the residual
     provider chose — i.e. the residual provider itself must EXPORT it — OR if the arrow is stated for
     ALL gates (like `hEmeas`) and a banked all-gate provider exists.  A caller can NEVER supply an
     arrow about the hidden `S` from outside.  This is why the narrow-route (fixed-`S`) providers
     (`endpointData_of_banked`, `interchangeData_of_banked`, `hDConv_from_banked`,
     `CConvFacade.hCConv_discharged_from_data`) do NOT discharge the wide antecedents: their per-`S`
     interface/analytic data is not available for the opaque provider-chosen `S`.

  ── THE CENSUS  (arrow → verdict → exact provider / gap).
     ┌─────────────┬───────────┬──────────────────────────────────────────────────────────────────┐
     │ arrow       │ verdict   │ provider / gap                                                    │
     ├─────────────┼───────────┼──────────────────────────────────────────────────────────────────┤
     │ hS0         │ BANKED    │ `GateOpennessExport.gatedWitnessN1_package_open` exports           │
     │ (0 ∈ S 0)   │ DISCHARGED│   `(0 ∈ K → 0 ∈ S 0)` for the SAME provider-chosen `S`; composed  │
     │             │           │   with the width-lift `ResidualAssemblyRecon.hEboundW_widen` into │
     │             │           │   `hEboundW_wide_from_geometry_open` (this file).  hS0 := hmemS0  │
     │             │           │   hK0.  Fully geometric — no new outer hyp.                       │
     ├─────────────┼───────────┼──────────────────────────────────────────────────────────────────┤
     │ hCH         │ BANKED    │ `InftyRebaseCapstone.hCH_discharge_from_geometry` from the same    │
     │ (C² witness)│ DISCHARGED│   package's `(0 ∈ K → IsOpen (S 0))` export + `{hg,hgiC,hgpos}`;  │
     │             │           │   needs the TWO extra geometry inputs `hgiC` (gi C^∞) and `hgpos` │
     │             │           │   (0 < det g) — both satisfiable, neither vacuous.               │
     ├─────────────┼───────────┼──────────────────────────────────────────────────────────────────┤
     │ hDuhamel    │ GENUINE   │ Levi/Duhamel ENDPOINT interface identity.  Narrow provider         │
     │             │           │   `TruncatedDuhamelData.endpointData_of_banked` builds it only    │
     │             │           │   from per-`S` `EndpointData`; not available for the opaque `S`.  │
     ├─────────────┼───────────┼──────────────────────────────────────────────────────────────────┤
     │ hInter      │ GENUINE   │ Levi INTERCHANGE (sum-swap) identity.  Narrow provider            │
     │             │           │   `TruncatedDuhamelData.interchangeData_of_banked` per-`S`; idem. │
     ├─────────────┼───────────┼──────────────────────────────────────────────────────────────────┤
     │ hDConv      │ PARTIAL   │ `HDConvThreading.hDConv_from_banked` exists but is CONDITIONAL on  │
     │ (Diff'able) │           │   the full analytic residue + the hard locally-uniform `Da`-limit │
     │             │           │   `hDaLimLU`; not a fully-geometric discharge, and per-`S`.       │
     ├─────────────┼───────────┼──────────────────────────────────────────────────────────────────┤
     │ hCConv      │ PARTIAL   │ `CConvFacade.hCConv_discharged_from_data` exists but needs the     │
     │ (C² heatConv)│          │   five CConv facade bundles (metric/chart/source/derivData/env)   │
     │             │           │   at the concrete gate; per-`S`, data-heavy, not pure geometry.   │
     ├─────────────┼───────────┼──────────────────────────────────────────────────────────────────┤
     │ hEmeas (S1) │ PARTIAL   │ `HEmeasBorelAudit.tripleHEmeas_of_surface` (from a                 │
     │ ∀-gate      │           │   `BorelDischargeSurface`) and the chart-wall-free                │
     │             │           │   `GcConsumerMirror.tripleHEmeas_Gc` bank S1 PER-(S,a,b) from a   │
     │             │           │   measurability bundle.  The capstone hyp is the `∀ S a b` gate   │
     │             │           │   (the residual provider chooses the gate existentially), and NO  │
     │             │           │   pure-geometry `∀ S a b, tripleHEmeas` provider is banked; nor   │
     │             │           │   can the ∀-gate be weakened to the provider-chosen instance —    │
     │             │           │   that `S` is not nameable at the binder site.  Kept as-is.       │
     └─────────────┴───────────┴──────────────────────────────────────────────────────────────────┘

  ── THE DISCHARGE.  `wide_a1_R6_interface_discharged` = `wide_a1_R6_both_slots_internal` with the two
     antecedents `hS0` and `hCH` REMOVED from the returned implication chain, supplied internally, at
     the cost of the two satisfiable geometry inputs `hgiC`/`hgpos`.  The returned implication is
     therefore `hDuhamel → hInter → hDConv → hCConv → <2-jet>` (shorter by exactly the `hS0` and `hCH`
     arrows).  Compiled source of `wide_a1_R6_both_slots_internal` is copied verbatim; the capstone
     statement is NOT reconstructed from scratch.

  ── DISTANCE-TO-`a₁=R/6` (the shortest capstone's carry list, honest):
       • `1 ≤ n`;
       • S1 `∀`-gate `∀ S a b, tripleHEmeas g gi (vanVleckGatedWitness …)`;
       • base geometry `hChr/hK/hK0/hg/hgiC/hgpos/hg0/hgi/hΓ/hdg0/htr/hsrc/hgnd/hgsymm/hinvF/hframeK/hw`;
       • the surviving inner interface antecedents `hDuhamel/hInter/hDConv/hCConv` (Levi/Duhamel + the
         single spatial-`C²` heatConv slot — the CITED analytic frontier, per-`S`, never the
         conclusion).

  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypotheses.  Every carried hypothesis is satisfiable, non-vacuous, and NEVER equal to the
  conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.WideA1AssemblyTrunc
import QIQTH.GateOpennessExport
import QIQTH.InftyRebaseCapstone

open MeasureTheory Finset Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.RadialTransport
open QIQTH.ParametrixFunction QIQTH.VanVleck QIQTH.HeatTransportRecursion
open QIQTH.VanVleckCancellation QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.HeatParametrixAnsatz QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.ErrorKernelFactorization
open QIQTH.OmegaHsrcC4cAudit QIQTH.CConvFacade QIQTH.GateOpennessExport
open QIQTH.TruncatedHIntRethread QIQTH.ResidualAssemblyRecon
open QIQTH.DataPileWitnessAudit QIQTH.HEmeasBorelAudit QIQTH.PullbackMetric
open QIQTH.InftyRebaseCapstone QIQTH.WideA1AssemblyTrunc
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.InterfaceArrowCensus

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ###############################################################################
    ### 1. THE STRENGTHENED WIDE GEOMETRY PROVIDER — bound + gate-centre EXPORTS.
    ############################################################################### -/

/-- **★★★ J4-264 (1) — `hEboundW_wide_from_geometry_open`.**  The width-`κ` (`κ ≥ 2`) residual
    provider `ResidualAssemblyRecon.hEboundW_wide_from_geometry` STRENGTHENED to ALSO export the
    origin gate-centre membership `(0 ∈ K → 0 ∈ S 0)` and the origin gate-openness
    `(0 ∈ K → IsOpen (S 0))` for the SAME provider-chosen gate `S`.  Built by composing
    `GateOpennessExport.gatedWitnessN1_package_open` (the width-2 bound + the two gate exports on one
    shared `S`) with the width-lift `hEboundW_widen`.  The width-lift touches only the domination
    constant, so both gate exports carry through verbatim.  This is exactly what lets the wide capstone
    discharge `hS0`/`hCH` internally.  NOT `a₁ = R/6`. -/
theorem hEboundW_wide_from_geometry_open (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (t : ℝ) (ht : 0 ≤ t) (κ : ℝ) (hκ : 2 ≤ κ) :
    ∃ a b C'' : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C'' ∧ ∃ S : Point n → Set (Point n),
      (∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ C'' * baseKernelW κ (0 : ℝ) τ p q)
      ∧ ((0 : Point n) ∈ K → (0 : Point n) ∈ S 0)
      ∧ ((0 : Point n) ∈ K → IsOpen (S 0)) := by
  obtain ⟨a, b, C, ha, hab, hC0, S, hbound, hmemS0, hopenS0⟩ :=
    gatedWitnessN1_package_open g gi hg hChr hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
  -- fix the outer time `t`: the width-2 bound in `vanVleckGatedWitness` form (defeq to `gatedKernel`).
  have hbound_t : ∀ τ p q, 0 < τ → τ ≤ t →
      |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
        ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
    intro τ p q hτ hτt; exact hbound t τ p q hτ hτt
  refine ⟨a, b, (C * (1 + t)) * Real.sqrt (κ / 2) ^ n, ha, hab,
    mul_nonneg (mul_nonneg hC0 (by linarith)) (by positivity), S, ?_, hmemS0, hopenS0⟩
  exact hEboundW_widen g gi (vanVleckGatedWitness g gi hChr hK S a b)
    (mul_nonneg hC0 (by linarith)) hκ hbound_t

/-! ###############################################################################
    ### 2. THE DISCHARGE — `hS0` AND `hCH` internalized; interface chain shorter by 2.
    ############################################################################### -/

/-- **★★★★ `wide_a1_R6_interface_discharged` (THE PRIZE — J4-264).**  Exactly
    `WideA1AssemblyTrunc.wide_a1_R6_both_slots_internal` with the two inner interface antecedents
    `hS0 : 0 ∈ S 0` and `hCH : ContDiffAt ℝ 2 (fun p ↦ vanVleckGatedWitness … t p 0) 0` REMOVED from
    the returned implication chain and supplied INTERNALLY: the gate `S` is now sourced from the
    strengthened provider `hEboundW_wide_from_geometry_open` (§1), whose gate exports give `hS0`
    (`hmemS0 hK0`) and gate-openness `hSopen` (`hopenS0 hK0`), and `hCH` follows from
    `InftyRebaseCapstone.hCH_discharge_from_geometry` on `{hg, hgiC, hgpos}`.  Two satisfiable geometry
    inputs the discharge requires — `hgiC` (inverse metric `C^∞`) and `hgpos` (positive metric
    determinant) — are added; both are honest geometry, neither vacuous nor the conclusion.  Relative
    to `wide_a1_R6_both_slots_internal` the returned implication is SHORTER by exactly the `hS0` and
    `hCH` arrows; the surviving interface antecedents are `hDuhamel → hInter → hDConv → hCConv`.  BOTH
    residual slots stay internal (`hEboundW_le` from the provider, `hInt` from the truncated producer)
    and S1 is carried `∀`-gate.  ⚠ STILL NOT `a₁ = R/6`. -/
theorem wide_a1_R6_interface_discharged
    (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (κ : ℝ) (hκ : 2 ≤ κ) (hn : 1 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hEmeas : ∀ (S : Point n → Set (Point n)) (a b : ℝ),
      tripleHEmeas g gi (vanVleckGatedWitness g gi hChr hK S a b)) :
    ∃ a b C' : ℝ, ∃ S : Point n → Set (Point n),
      0 < a ∧ a < b ∧ 0 ≤ C' ∧
      ((heatOp g gi (fun u p q => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u p q) t 0 0
            = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) t 0 0
              + heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
                  (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0) →
        (heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0
            = ∑' k : ℕ, heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
                (fun τ p q => (-1 : ℝ) ^ (k + 1)
                  * iterE (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) (k + 1) τ p q)
                t 0 0) →
        DifferentiableAt ℝ (fun u => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) u 0 0) t →
        ContDiffAt ℝ 2 (fun p => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t p 0)
            (0 : Point n) →
        heatOp g gi (trueHeatKernel (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))) t 0 0 = 0
        ∧ trueHeatKernel (vanVleckGatedWitness g gi hChr hK S a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0
            = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
              * (1 + ((∑ i, Ric i i) / 6) * t
                  + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                              transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                                * t ^ (k - 2))
                            + heatConv (vanVleckGatedWitness g gi hChr hK S a b)
                                (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)))
                                t 0 0
                                / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2)))) := by
  have hκ0 : (0 : ℝ) < κ := by linarith
  obtain ⟨a, b, C', ha, hab, hC0, S, hbound, hmemS0, hopenS0⟩ :=
    hEboundW_wide_from_geometry_open g gi hChr hK hg hgnd hgsymm hinvF hframeK hw hdg0 hg0 t ht.le κ hκ
  refine ⟨a, b, C', S, ha, hab, hC0, ?_⟩
  intro hDuhamel hInter hDConv hCConv
  have hg0' : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    intro i j; rw [hg0, Matrix.one_apply]
  -- ★ DISCHARGE 1: gate-centre membership `hS0`, FREE from the provider's exported field.
  have hS0 : (0 : Point n) ∈ S 0 := hmemS0 hK0
  have hSopen : IsOpen (S 0) := hopenS0 hK0
  -- ★ DISCHARGE 2: the spatial-`C²` witness-diagonal slot `hCH`, from `C^∞` geometry alone.
  have hCH : ContDiffAt ℝ 2 (fun p => vanVleckGatedWitness g gi hChr hK S a b t p 0) (0 : Point n) :=
    hCH_discharge_from_geometry g gi hChr hK S a b t hK0 hS0 hSopen hg hgiC hgpos hg0'
  -- INTERNALIZE `hInt` from the SAME fixed-`C'` `τ ≤ t` residual bound via the truncated producer.
  have hInt : IterConvIntegrableWOn
      (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) κ 0 C' t :=
    iterConvIntegrableWOn_of_bound_baseMeas_trunc
      (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) κ C' t hκ0 hbound
      (hEzeroE_concrete g gi hChr hK S a b hn) (hEmeas S a b)
  exact wide_a1_R6_of_residue_inf_trunc g gi Ric t ht C' hC0 κ hκ0 hChr hK S a b ha hab hK0 hS0
    (vanVleckGatedWitness g gi hChr hK S a b) rfl hg hg0' hgi hΓ hdg0 htr hsrc
    hbound hInt hDuhamel hInter hDConv hCH hCConv

end QIQTH.InterfaceArrowCensus

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.InterfaceArrowCensus
#print axioms hEboundW_wide_from_geometry_open
#print axioms wide_a1_R6_interface_discharged
end AxiomChecks
