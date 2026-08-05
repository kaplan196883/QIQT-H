/-
  ProviderSideExports — J4-265: provider-side EXPORT of the `hInter` interface arrow, and the
  wide `a₁` residual capstone with `hInter` discharged.  ONE brick of the `a₁ = R/6` heat-kernel
  campaign.  NOT `a₁ = R/6`; proves NOTHING new about `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  This file carries NO coefficient/geometry content of its own.  It performs ONE
  further mechanical rewiring of the ALREADY-BANKED wide capstone
  `InterfaceArrowCensus.wide_a1_R6_interface_discharged` (J4-264), whose returned implication was
  `hDuhamel → hInter → hDConv → hCConv → <a₁ two-jet>` with the four antecedents referencing the
  PROVIDER-CHOSEN gate `S` (existential in the ∃-conclusion).  A caller can never supply an arrow about
  that hidden `S` from outside; the only route is for the residual provider to EXPORT the fact for the
  SAME `S` it chose.  Here we EXPORT `hInter`.

  ── WHY `hInter` EXPORTS (the tractable arrow).  `hInter` is the tsum/heatConv INTERCHANGE identity at
     `t, 0, 0`.  The banked windowed provider `InterchangeLocalRebase.hInter_from_local_data` (J4-206)
     produces EXACTLY that identity from four inputs, ALL of which are available at the concrete gate
     that `GateOpennessExport.gatedWitnessN1_package_open` chooses:
       • `hEbnd`   — the `(0,t]` fixed-constant one-step Gaussian bound.  The package exports the ALL-`t`
                     family `∀ t', ∀ τ p q, 0<τ→τ≤t'→ |heatOp …| ≤ (C·(1+t'))·baseKernelW 2 0 τ p q`,
                     so the `t' := t` slice is `hEbnd` at `C := C·(1+t)`.
       • `hEzero`  — nonpositive-time vanishing, DISCHARGED from geometry by
                     `DataPileWitnessAudit.hEzeroE_concrete` (needs `1 ≤ n`).
       • `hEmeas`  — the base joint strong measurability of `heatOp`, carried `∀`-gate (`tripleHEmeas`)
                     exactly as `wide_a1_R6_interface_discharged` already carries it.
       • `hglobal` — the every-ceiling bound family, supplied by the SAME all-`t` package export
                     (`fun T' _ => ⟨C·(1+T'), …, package-bound at t' := T'⟩`).  This is the crux: the
                     package's bound is universally quantified over the ceiling, so no all-τ envelope is
                     missing — every window has its own fixed constant.
     The interchange is a WIDTH-2 fact; `hInter` is width-free, so it feeds the width-`κ` capstone
     unchanged.

  ── WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; each std-3):
     • `hEboundW_wide_from_geometry_open_inter` — the strengthened residual provider: the width-`κ`
       `(0,t]` bound + the two gate-centre exports (`0 ∈ K → 0 ∈ S 0`, `0 ∈ K → IsOpen (S 0)`) of
       `InterfaceArrowCensus.hEboundW_wide_from_geometry_open`, PLUS the exported interchange identity
       `hInter` at `t, 0, 0`, ALL for the SAME provider-chosen gate `S`.  It adds the two satisfiable
       inputs `ht : 0 < t` (strict, the interchange needs it) and `hn : 1 ≤ n` (for `hEzero`), and the
       `∀`-gate measurability `hEmeas` (identical to the capstone's own carry).
     • `wide_a1_R6_interface_discharged_v2` — `wide_a1_R6_interface_discharged` with the `hInter`
       antecedent REMOVED from the returned implication and supplied INTERNALLY from the provider export.
       The returned implication drops to `hDuhamel → hDConv → hCConv → <a₁ two-jet>` (shorter by exactly
       the `hInter` arrow).  Every base geometry / measurability input is unchanged; the `hEmeas` `∀`-gate
       is now ALSO consumed to build the exported `hInter` (it was already consumed for `hInt`).

  ── DEFINITIVE CARRY LIST of `wide_a1_R6_interface_discharged_v2` (honest; all satisfiable, non-vacuous,
     never the conclusion):
       • `1 ≤ n`;
       • the S1 `∀`-gate `∀ S a b, tripleHEmeas g gi (vanVleckGatedWitness …)`;
       • base geometry `hChr/hK/hK0/hg/hgiC/hgpos/hg0/hgi/hΓ/hdg0/htr/hsrc/hgnd/hgsymm/hinvF/hframeK/hw`;
       • the SURVIVING inner interface antecedents `hDuhamel/hDConv/hCConv` (Levi/Duhamel truncated
         identity + the two spatial-`C²` slots — the CITED analytic frontier, per-`S`, never the
         conclusion).  `hInter` is NO LONGER carried.

  ── UPDATED CENSUS (arrows of the returned implication):
       hS0     — discharged (J4-264, gate export).
       hCH     — discharged (J4-264, geometry).
       hInter  — DISCHARGED HERE (this file, provider-side export via the windowed interchange).
       hDuhamel — still antecedent (Levi/Duhamel truncated identity; `truncatedDuhamelCore_of_daLim`
                  rests on the loc-unif `hDaLimLU` WALL).
       hDConv  — still antecedent (`HDConvThreading.hDConv_from_banked`; near-diagonal ODE / sliver).
       hCConv  — still antecedent (`CConvFacade.hCConv_discharged_from_data`; five facade bundles).

  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypotheses.  Every carried hypothesis is satisfiable, non-vacuous, and NEVER equal to the
  conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.InterfaceArrowCensus
import QIQTH.InterchangeLocalRebase

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

namespace QIQTH.ProviderSideExports

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ###############################################################################
    ### 1. THE STRENGTHENED WIDE GEOMETRY PROVIDER — bound + gate EXPORTS + `hInter`.
    ############################################################################### -/

/-- **★★★ J4-265 (1) — `hEboundW_wide_from_geometry_open_inter`.**  The strengthened residual provider
    `InterfaceArrowCensus.hEboundW_wide_from_geometry_open` (width-`κ` `(0,t]` bound + the two gate-centre
    exports) ADDITIONALLY exporting the tsum/heatConv INTERCHANGE identity `hInter` at `t, 0, 0`, for the
    SAME provider-chosen gate `S`.  Built by (i) re-running `gatedWitnessN1_package_open` to get the
    ALL-`t` width-2 package bound + the two gate exports on one shared `S`, (ii) widening the `t`-slice to
    `κ` via `hEboundW_widen`, and (iii) feeding the all-`t` bound (both the `t`-window and the
    every-ceiling `hglobal` family) plus `hEzeroE_concrete` (needs `1 ≤ n`) and the carried `∀`-gate
    measurability into `InterchangeLocalRebase.hInter_from_local_data` at window `T := t`.  NOT
    `a₁ = R/6`. -/
theorem hEboundW_wide_from_geometry_open_inter (g gi : Point n → Fin n → Fin n → ℝ)
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
    (t : ℝ) (ht : 0 < t) (κ : ℝ) (hκ : 2 ≤ κ) (hn : 1 ≤ n)
    (hEmeas : ∀ (S : Point n → Set (Point n)) (a b : ℝ),
      tripleHEmeas g gi (vanVleckGatedWitness g gi hChr hK S a b)) :
    ∃ a b C'' : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C'' ∧ ∃ S : Point n → Set (Point n),
      (∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ C'' * baseKernelW κ (0 : ℝ) τ p q)
      ∧ ((0 : Point n) ∈ K → (0 : Point n) ∈ S 0)
      ∧ ((0 : Point n) ∈ K → IsOpen (S 0))
      ∧ (heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))) t 0 0
          = ∑' k : ℕ, heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b))
              (fun τ p q => (-1 : ℝ) ^ (k + 1)
                * iterE (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) (k + 1) τ p q)
              t 0 0) := by
  obtain ⟨a, b, C, ha, hab, hC0, S, hbound, hmemS0, hopenS0⟩ :=
    gatedWitnessN1_package_open g gi hg hChr hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
  -- The ALL-`t` width-2 bound in `vanVleckGatedWitness` form (defeq to the package's `gatedKernel` form).
  have hboundVW : ∀ t' τ p q, 0 < τ → τ ≤ t' →
      |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q :=
    fun t' τ p q hτ hτt => hbound t' τ p q hτ hτt
  have hCt0 : (0 : ℝ) ≤ C * (1 + t) := mul_nonneg hC0 (by linarith)
  refine ⟨a, b, (C * (1 + t)) * Real.sqrt (κ / 2) ^ n, ha, hab,
    mul_nonneg hCt0 (by positivity), S, ?_, hmemS0, hopenS0, ?_⟩
  · -- width-`κ` `(0,t]` bound from the width-2 `t`-slice via `hEboundW_widen`.
    exact hEboundW_widen g gi (vanVleckGatedWitness g gi hChr hK S a b) hCt0 hκ (hboundVW t)
  · -- exported `hInter` at `t, 0, 0` via the windowed interchange provider at `T := t`.
    exact QIQTH.InterchangeLocalRebase.hInter_from_local_data
      (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) (C * (1 + t)) t hCt0 ht
      (fun τ p q hτ hτt => hboundVW t τ p q hτ hτt)
      (hEzeroE_concrete g gi hChr hK S a b hn)
      (hEmeas S a b)
      (fun T' hT' => ⟨C * (1 + T'), mul_nonneg hC0 (by linarith),
        fun τ p q hτ hτT' => hboundVW T' τ p q hτ hτT'⟩)
      t ht le_rfl 0 0

/-! ###############################################################################
    ### 2. THE DISCHARGE — `hInter` internalized; interface chain shorter by 1.
    ############################################################################### -/

/-- **★★★★ `wide_a1_R6_interface_discharged_v2` (THE PRIZE — J4-265).**  Exactly
    `InterfaceArrowCensus.wide_a1_R6_interface_discharged` with the inner interface antecedent
    `hInter` (the tsum/heatConv interchange identity) REMOVED from the returned implication and supplied
    INTERNALLY: the gate `S` is sourced from the strengthened provider
    `hEboundW_wide_from_geometry_open_inter` (§1), whose exported interchange field is exactly the `hInter`
    slot for that same `S`.  All other discharges are unchanged (`hS0`/`hSopen` from the gate exports,
    `hCH` from `hCH_discharge_from_geometry`, `hInt` from the truncated producer).  Relative to
    `wide_a1_R6_interface_discharged` the returned implication is SHORTER by exactly the `hInter` arrow;
    the surviving interface antecedents are `hDuhamel → hDConv → hCConv`.  ⚠ STILL NOT `a₁ = R/6`. -/
theorem wide_a1_R6_interface_discharged_v2
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
  obtain ⟨a, b, C', ha, hab, hC0, S, hbound, hmemS0, hopenS0, hInter⟩ :=
    hEboundW_wide_from_geometry_open_inter g gi hChr hK hg hgnd hgsymm hinvF hframeK hw hdg0 hg0
      t ht κ hκ hn hEmeas
  refine ⟨a, b, C', S, ha, hab, hC0, ?_⟩
  intro hDuhamel hDConv hCConv
  have hg0' : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    intro i j; rw [hg0, Matrix.one_apply]
  -- ★ gate-centre membership + openness, FREE from the provider's exported fields.
  have hS0 : (0 : Point n) ∈ S 0 := hmemS0 hK0
  have hSopen : IsOpen (S 0) := hopenS0 hK0
  -- ★ the spatial-`C²` witness-diagonal slot `hCH`, from `C^∞` geometry alone.
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

end QIQTH.ProviderSideExports

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.ProviderSideExports
#print axioms hEboundW_wide_from_geometry_open_inter
#print axioms wide_a1_R6_interface_discharged_v2
end AxiomChecks
