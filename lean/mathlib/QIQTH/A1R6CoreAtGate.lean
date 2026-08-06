/-
  A1R6CoreAtGate — J4-338: v3-export brick 1.  The a₁ two-jet CONCLUSION exported at the LITERAL
  constant-radius gate, from {base geometry/gauge + hS1 + htr + the three slot antecedents}, with NO
  existential and NO labelled inputs.  ONE brick of the `a₁ = R/6` heat-kernel campaign.

  ⚠ HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  The exported
  core `wide_a1_R6_core_AT_CONSTRADIUS` is a CONDITIONAL implication: its conclusion (the a₁ two-jet at
  the concrete gate) holds ONLY given its antecedents (the three per-gate analytic slots
  `hDuhamel/hDConv/hCConv`, the S1 measurability `hS1`, the geometry gauge `htr`, and the package's
  Gaussian bound).  The genuinely labelled inputs (hGauss/hraw/hD2Hexpand/hPd2conv) enter only at v3
  brick 5 (`a1_R6_from_labelled`), which will feed this core.  Nothing here is closer to `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (K0) RECON — the pre-∃ inner theorem, mapped from `wide_a1_R6_interface_discharged_v2`'s PROOF.

  ── THE PROOF STRUCTURE of `ProviderSideExports.wide_a1_R6_interface_discharged_v2` (its `by`-block):
       1. `obtain ⟨a,b,C',ha,hab,hC0,S,hbound,hmemS0,hopenS0,hInter⟩ :=`
             `hEboundW_wide_from_geometry_open_inter …`   -- the provider chooses the (existential) gate `S`
                                                          -- and exports the bound + gate exports + `hInter`.
       2. `refine ⟨a,b,C',S,ha,hab,hC0, ?_⟩; intro hDuhamel hDConv hCConv`
       3. `have hS0 := hmemS0 hK0`, `have hSopen := hopenS0 hK0`     -- gate-centre exports.
       4. `have hCH := hCH_discharge_from_geometry … hK0 hS0 hSopen hg hgiC hgpos hg0'`  -- C² diagonal slot.
       5. `have hInt := iterConvIntegrableWOn_of_bound_baseMeas_trunc … hbound (hEzeroE_concrete …) …`
       6. `exact wide_a1_R6_of_residue_inf_trunc g gi Ric t ht C' hC0 κ hκ0 hChr hK S a b ha hab hK0 hS0`
             `(vanVleckGatedWitness …) rfl hg hg0' hgi hΓ hdg0 htr hsrc`
             `hbound hInt hDuhamel hInter hDConv hCH hCConv`
     The theorem applied IMMEDIATELY BEFORE the `∃`-intro (step 6, after the `refine` at step 2 has
     already introduced the `∃`) — i.e. the inner theorem that carries the implication chain
     `(hDuhamel → hDConv → hCConv → ⟨a₁ two-jet⟩)` while `S` is still CONCRETE — is:

        ★ `QIQTH.WideA1AssemblyTrunc.wide_a1_R6_of_residue_inf_trunc`  (WideA1AssemblyTrunc.lean:191).

  ── VERDICT: **O2** (the inner theorem is public and nameable).  Brick 1 is therefore a THIN
     apply-wrapper at the literal gate: the same lower-level lemmas (steps 3–6) are replayed with the
     provider-chosen `S` replaced by the CONSTANT-radius gate
     `constGate g gi hChr hK c = fun z => uniformFlowExp g gi hChr hK z '' Metric.ball 0 c`
     (the J4-316 `gatedWitnessN1_package_open_CONSTRADIUS` literal gate).  No re-derivation (O3) needed.

  ── THE INNER THEOREM'S HYPOTHESIS LIST (`wide_a1_R6_of_residue_inf_trunc`, at the point where `S` is
     concrete — copied verbatim, the arguments the core must supply):
       g gi Ric · t (ht : 0<t) · C (hCnn : 0≤C) · κ (hκ : 0<κ) ·
       hChr {K} hK S a b (ha : 0<a) (hab : a<b) hK0 hS0 ·
       H (hHeq : H = vanVleckGatedWitness g gi hChr hK S a b) ·
       hg · hg0 (MATRIX form) · hgi · hΓ · hdg0 · htr · hsrc ·
       hEboundW_le  (the (0,t] width-κ Gaussian bound, fixed constant) ·
       hInt         (IterConvIntegrableWOn — DERIVED here from the bound + hEzero + hS1) ·
       hDuhamel     (SLOT antecedent — kept flat) ·
       hInter       (interchange identity — DERIVED here via `hInter_from_local_data`) ·
       hDConv       (SLOT antecedent — kept flat) ·
       hCH          (C² diagonal — DERIVED here via `hCH_discharge_from_geometry`) ·
       hCConv       (SLOT antecedent — kept flat).
     Conclusion: the a₁ two-jet (`heatOp … trueHeatKernel … = 0 ∧ trueHeatKernel … = heatKernel1D^n·(…)`).

  ── HOW THE CONSTRADIUS PACKAGE FEEDS IT (K0 (2)).  The J4-316 package
     `gatedWitnessN1_package_open_CONSTRADIUS` / `constRadius_package_and_S1` provides, at the LITERAL
     gate, exactly the fields the inner theorem's DERIVED slots consume:
       • the ALL-`t` width-2 bound  `∀ t', ∀ τ p q, 0<τ→τ≤t' → |heatOp …| ≤ (C·(1+t'))·baseKernelW 2 0 τ p q`
         → its `t' := t` slice IS `hEboundW_le` (κ := 2, fixed constant `C·(1+t)`), and its full family IS
           the `hglobal` envelope `hInter_from_local_data` needs;
       • the two gate-centre exports `(0∈K → 0 ∈ S 0)`, `(0∈K → IsOpen (S 0))` → `hS0`, `hSopen`;
       • `hS1 : tripleHEmeas g gi (vanVleckGatedWitness g gi hChr hK (constGate …) a b)` = the S1
         measurability (defeq `StronglyMeasurable …`), feeding BOTH `hInt` and `hInter`.
     `hEzeroE_concrete` supplies the nonpositive-time vanishing from geometry (needs `1 ≤ n`).

  ## (K1) THE DELIVERABLE — `wide_a1_R6_core_AT_CONSTRADIUS`.
  The a₁ two-jet at the literal gate, from {base geometry/gauge (the v2 capstone's NON-slot antecedents,
  minus the over-general ∀-gate `hEmeas` — replaced by the per-gate `hS1` — and with `htr` kept explicit
  for brick 2), the package's bound + the two gate-centre exports + `hS1`, `htr`, and the three flat
  slot antecedents `hDuhamel/hDConv/hCConv`}.  Proof = five typed `have`s (`hg0'`, `hS0`, `hSopen`, the
  bound slice, `hEz`, `hInt`, `hInter`, `hCH`) then ONE heavy application of the inner theorem.  Width
  is pinned to `κ := 2` (the package's native width), so NO widening lemma is needed.  No `sorry`, no new
  axioms, no `:= True`, no vacuous / unsatisfiable hypotheses; NONE of the hypotheses is the conclusion.
  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.InterfaceArrowCensus
import QIQTH.InterchangeLocalRebase
import QIQTH.ConstRadiusGateExport

open MeasureTheory Finset Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.RadialTransport
open QIQTH.ParametrixFunction QIQTH.VanVleck QIQTH.HeatTransportRecursion
open QIQTH.VanVleckCancellation QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.HeatParametrixAnsatz QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.ErrorKernelFactorization
open QIQTH.OmegaHsrcC4cAudit QIQTH.CConvFacade QIQTH.GateOpennessExport
open QIQTH.TruncatedHIntRethread QIQTH.ResidualAssemblyRecon
open QIQTH.DataPileWitnessAudit QIQTH.HEmeasBorelAudit QIQTH.PullbackMetric
open QIQTH.InftyRebaseCapstone QIQTH.WideA1AssemblyTrunc QIQTH.ExpMap
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.A1R6CoreAtGate

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-- **The one shared syntactic gate.**  The J4-316 `gatedWitnessN1_package_open_CONSTRADIUS` literal
    constant-radius flow-ball gate `fun z => uniformFlowExp g gi hChr hK z '' Metric.ball 0 c`.  NOT
    `a₁ = R/6`. -/
noncomputable def constGate (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (c : ℝ) : Point n → Set (Point n) :=
  fun z => uniformFlowExp g gi hChr hK z '' Metric.ball (0 : Point n) c

/-! ###############################################################################
    ### THE CORE — a₁ two-jet at the literal constant-radius gate (O2 apply-wrapper).
    ############################################################################### -/

/-- **★★★★ J4-338 (K1) — `wide_a1_R6_core_AT_CONSTRADIUS`.**  The a₁ two-jet CONCLUSION at the literal
    constant-radius gate `constGate g gi hChr hK c`, derived from: the base geometry/gauge antecedents
    (the `wide_a1_R6_interface_discharged_v2` NON-slot binders, minus the over-general ∀-gate `hEmeas`,
    replaced by the per-gate `hS1`, and with `htr` kept explicit); the constant-radius package's ALL-`t`
    width-2 Gaussian bound `hpkgBound` + the two gate-centre exports `hmemS0`/`hopenS0`; the S1
    measurability `hS1` at that same gate; and the three FLAT per-gate analytic slots
    `hDuhamel`/`hDConv`/`hCConv`.  Internally it discharges `hS0`, `hSopen`, `hEz` (nonpositive-time
    vanishing), `hInt` (iterated-convolution integrability), `hInter` (the tsum/heatConv interchange),
    and `hCH` (the C² diagonal), then applies the pre-∃ inner theorem
    `WideA1AssemblyTrunc.wide_a1_R6_of_residue_inf_trunc` ONCE, at width `κ := 2`.  NO existential, NO
    labelled inputs (those enter only at brick 5).  ⚠ This is a CONDITIONAL implication — NOT
    `a₁ = R/6`. -/
theorem wide_a1_R6_core_AT_CONSTRADIUS
    (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (hn : 1 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (a b c C : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c) (hCnn : 0 ≤ C)
    (htr : ∀ cc d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) cc 0) = -(2 / 3) * Ric cc d)
    -- ── the J4-316 constant-radius package fields at `(a,b,c,C)` (fed by brick 5 from `constRadius_package_and_S1`):
    (hpkgBound : ∀ t' : ℝ, ∀ τ p q, 0 < τ → τ ≤ t' →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hmemS0 : (0 : Point n) ∈ K → (0 : Point n) ∈ constGate g gi hChr hK c 0)
    (hopenS0 : (0 : Point n) ∈ K → IsOpen (constGate g gi hChr hK c 0))
    -- ── the S1 measurability at that SAME literal gate (`hEmeasBorelAudit.tripleHEmeas`):
    (hS1 : QIQTH.HEmeasBorelAudit.tripleHEmeas g gi
      (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))
    -- ── the three FLAT per-gate analytic slots (verbatim capstone antecedent shapes at `constGate … c`):
    (hDuhamel : heatOp g gi (fun u p q =>
          heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
            u p q) t 0 0
        = leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)) t 0 0
          + heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))
              (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
              t 0 0)
    (hDConv : DifferentiableAt ℝ
        (fun u => heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
          u 0 0) t)
    (hCConv : ContDiffAt ℝ 2
        (fun p => heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
          (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
          t p 0)
        (0 : Point n)) :
    heatOp g gi (trueHeatKernel (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))) t 0 0 = 0
    ∧ trueHeatKernel (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, Ric i i) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
                            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
                            t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  -- the matrix-valued form of the flat-metric gauge at the origin.
  have hg0' : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    intro i j; rw [hg0, Matrix.one_apply]
  -- gate-centre membership + openness, FREE from the package's exported fields.
  have hS0 : (0 : Point n) ∈ constGate g gi hChr hK c 0 := hmemS0 hK0
  have hSopen : IsOpen (constGate g gi hChr hK c 0) := hopenS0 hK0
  -- the fixed-`t` width-2 slice of the package bound (constant `C·(1+t)`).
  have hCt0 : (0 : ℝ) ≤ C * (1 + t) := mul_nonneg hCnn (by linarith)
  have hbound_slice : ∀ τ p q, 0 < τ → τ ≤ t →
      |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
        ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q :=
    fun τ p q hτ hτt => hpkgBound t τ p q hτ hτt
  -- nonpositive-time vanishing, from geometry (needs `1 ≤ n`).
  have hEz : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n,
      heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q = 0 :=
    hEzeroE_concrete g gi hChr hK (constGate g gi hChr hK c) a b hn
  -- the iterated-convolution integrability slot, from the bound + hEz + hS1 (truncated producer).
  have hInt : IterConvIntegrableWOn
      (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))
      (2 : ℝ) 0 (C * (1 + t)) t :=
    iterConvIntegrableWOn_of_bound_baseMeas_trunc
      (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))
      (2 : ℝ) (C * (1 + t)) t (by norm_num) hbound_slice hEz hS1
  -- the tsum/heatConv interchange identity, from the same data + the ALL-`t` envelope.
  have hInter : heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) t 0 0
      = ∑' k : ℕ, heatConv (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))
          (fun τ p q => (-1 : ℝ) ^ (k + 1)
            * iterE (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))
                (k + 1) τ p q) t 0 0 :=
    QIQTH.InterchangeLocalRebase.hInter_from_local_data
      (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))
      (C * (1 + t)) t hCt0 ht hbound_slice hEz hS1
      (fun T' hT' => ⟨C * (1 + T'), mul_nonneg hCnn (by linarith),
        fun τ p q hτ hτT' => hpkgBound T' τ p q hτ hτT'⟩)
      t ht le_rfl 0 0
  -- the spatial-C² witness-diagonal slot, from C^∞ geometry alone.
  have hCH : ContDiffAt ℝ 2
      (fun p => vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b t p 0) (0 : Point n) :=
    hCH_discharge_from_geometry g gi hChr hK (constGate g gi hChr hK c) a b t hK0 hS0 hSopen
      hg hgiC hgpos hg0'
  -- ★ THE ONE HEAVY APPLICATION — the pre-∃ inner theorem at the concrete gate, width `κ := 2`.
  exact wide_a1_R6_of_residue_inf_trunc g gi Ric t ht (C * (1 + t)) hCt0 (2 : ℝ) (by norm_num)
    hChr hK (constGate g gi hChr hK c) a b ha hab hK0 hS0
    (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) rfl
    hg hg0' hgi hΓ hdg0 htr hsrc hbound_slice hInt hDuhamel hInter hDConv hCH hCConv

end QIQTH.A1R6CoreAtGate

/-! ## Axiom check — the core is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.A1R6CoreAtGate
#print axioms wide_a1_R6_core_AT_CONSTRADIUS
end AxiomChecks
