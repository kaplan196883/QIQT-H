/-
  LeviCarriesAssembly — J4-203: the inner-carry assembly of the `∞`-capstone.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It performs ONE
  mechanical rewiring of the ALREADY-BANKED `∞`-capstone (`EboundWiringHD1.a1_R6_of_residue_inf_v2`,
  itself `OmegaHsrcC4cAudit.a1_R6_of_residue_inf` with the `hEboundW_le` carry discharged):

    • `a1_R6_of_residue_inf_v3` — `a1_R6_of_residue_inf_v2` with the gate-centre membership carry
      `hS0 : 0 ∈ S 0` DISCHARGED internally.  The `v2` capstone obtained its gate map `S` from the
      OPAQUE existential of `CoeffU1Fix.gatedWitnessN1_hEboundW_le_vanVleck_final`, which exposes NO
      geometry of `S`, so no downstream consumer could ever satisfy `0 ∈ S 0`.  `v3` instead sources the
      SAME `(0,t]`-restricted width-2 bound from the STRENGTHENED provider
      `GatedWitnessPackage.gatedWitnessN1_package`, whose existential additionally exports
      `(0 ∈ K → 0 ∈ S 0)` for the very same `.choose`-built flow-ball gate `S q = φ_q '' ball 0 (cf q)`
      (base membership from `uniformFlowExp_zero`: `φ_q 0 = q`).  With `hK0 : 0 ∈ K` in hand the gate
      centre membership is FREE, so the inner carry list shrinks by exactly the `hS0` slot.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  THE PROVIDER MAP — the remaining inner carries `{hInt, hDuhamel, hInter, hDConv}` and their banked
  providers (each verified below; NONE composes into a NET reduction — every provider RELOCATES its
  clean implication-slot into a larger residue bundle whose core is a genuine wall, so all four STAY
  carried in `v3`; this is the honest verdict, not a wiring failure):

    • `hS0`      — **DISCHARGED** (this file), the sole net reduction.  Provider
                   `gatedWitnessN1_package` field `(0 ∈ K → 0 ∈ S 0)`, applied to `hK0`.
    • `hInt`     — provider `GatedWitnessPackage.leviSeries_gatedWitnessN1_dominated` /
                   `iterConvIntegrableW_of_locally_bound_baseMeas`: reduces `IterConvIntegrableW` to the
                   banked local bound + `hEzero` PLUS the M1 joint strong measurability `hEmeas`.  Shape
                   matches; irreducible residue = `hEmeas` (the M1 wall).  STAYS carried.
    • `hInter`   — provider `LeviInterchange.heatConv_leviSeries_interchange`: discharges the
                   tsum/heatConv interchange from `{hEbound, hEzero, hEmeas}`.  ⚠ MISMATCH: its `hEbound`
                   is GLOBAL-in-`τ` with a FIXED constant `C`, whereas the banked bound is `(0,t]`-local
                   with `C·(1+t)`; wiring needs a global-bound bridge (plus `hEmeas`).  STAYS carried.
    • `hDuhamel` — provider `SliverSumPlumbing.hDuhamel_semifinal` /
                   `InterchangeThreading.hDuhamel_penultimate`: output matches VERBATIM with
                   `F := leviSeries (heatOp g gi H)`, but consuming it trades ONE clean slot for a ~40-
                   hypothesis geometric/analytic bundle (interchange engine, integrability, sliver
                   amplitudes, domination, F2-regularity, measurability).  NET EXPANSION ⟹ NOT wired.
    • `hDConv`   — provider `ConvCarriesDischarge.hDConv_gatedWitnessN1_of_delta_final`: shape matches
                   for the concrete van-Vleck witness, but relocates the slot to
                   `{hDelta (the singular Lemma-3.14 delta-family limit), hMeasFII, hpar/htime/hR}`.
                   Irreducible core = `hDelta`.  STAYS carried.
    • `hCH`      — census-handled separately (`InftyRebaseCapstone.hCH_discharge_from_geometry`, which
                   now has `hS0` in hand but still needs `hSopen : IsOpen (S 0)` — NOT exported by the
                   package).  STAYS carried here.
    • `hCConv`   — the L2 facade + `hD1` slot (interface-closed in J4-202).  STAYS carried here.

  DEFINITIVE `v3` RESIDUE (the inner carry list AFTER this brick):
      `{hInt, hDuhamel, hInter, hDConv, hCH, hCConv}`  — exactly `v2`'s inner list MINUS `hS0`.

  No conclusion-in-disguise; no vacuous / unsatisfiable hypotheses; NO `sorry`; NO new axioms.
  The main is std-3.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.OmegaHsrcC4cAudit
import QIQTH.ConvApproximants

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.PullbackMetric
open QIQTH.HeatParametrixAnsatz QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.OmegaHsrcC4cAudit
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.LeviCarriesAssembly

variable {n : ℕ}

/-- **★★★ J4-203 — `a1_R6_of_residue_inf_v3`.**  `EboundWiringHD1.a1_R6_of_residue_inf_v2` with the
    gate-centre membership carry `hS0 : 0 ∈ S 0` DISCHARGED internally.  The provider is swapped from
    the opaque `gatedWitnessN1_hEboundW_le_vanVleck_final` to the STRENGTHENED
    `GatedWitnessPackage.gatedWitnessN1_package`, which exports, for the SAME shared flow-ball gate `S`,
    both the `(0,t]`-restricted width-2 bound (verbatim) AND `(0 ∈ K → 0 ∈ S 0)`; with `hK0` this makes
    the gate-centre membership FREE.  Relative to `v2` the inner carry list is shorter by exactly the
    `hS0` slot; the remaining inner carries `{hInt, hDuhamel, hInter, hDConv, hCH, hCConv}` are the
    Levi/Duhamel interface + the two field-`C²` slots (satisfiable interface assembly, never the
    conclusion).  ⚠ STILL NOT `a₁ = R/6`. -/
theorem a1_R6_of_residue_inf_v3 (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
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
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k)) :
    ∃ a b C' : ℝ, ∃ S : Point n → Set (Point n),
      0 < a ∧ a < b ∧ 0 ≤ C' ∧
      (IterConvIntegrableW (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) 2 0 C' →
        (heatOp g gi (fun u p q => heatConv (vanVleckGatedWitness g gi hChr hK S a b)
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
        ContDiffAt ℝ 2 (fun p => vanVleckGatedWitness g gi hChr hK S a b t p 0) (0 : Point n) →
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
  obtain ⟨a, b, C, ha, hab, hC0, S, hbound, hgate, hmemS0, hD1, hW00⟩ :=
    gatedWitnessN1_package g gi hg hChr hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
  refine ⟨a, b, C * (1 + t), S, ha, hab, mul_nonneg hC0 (by linarith), ?_⟩
  intro hInt hDuhamel hInter hDConv hCH hCConv
  -- ★ the sole discharge: the gate-centre membership is FREE from the package's exported field.
  have hS0 : (0 : Point n) ∈ S 0 := hmemS0 hK0
  have hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ t →
      |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
        ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
    intro τ p q hτ hτt
    exact hbound t τ p q hτ hτt
  have hg0' : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    intro i j; rw [hg0, Matrix.one_apply]
  exact a1_R6_of_residue_inf g gi Ric t ht (C * (1 + t)) (mul_nonneg hC0 (by linarith))
    hChr hK S a b ha hab hK0 hS0 (vanVleckGatedWitness g gi hChr hK S a b) rfl
    hg hg0' hgi hΓ hdg0 htr hsrc hEboundW_le hInt hDuhamel hInter hDConv hCH hCConv

end QIQTH.LeviCarriesAssembly

section AxiomChecks
open QIQTH.LeviCarriesAssembly
#print axioms a1_R6_of_residue_inf_v3
end AxiomChecks
