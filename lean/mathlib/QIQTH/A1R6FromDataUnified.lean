/-
  A1R6FromDataUnified — J4-749: THE UNIFIED CAPSTONE `a1_R6_from_data_v5`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It only
  UNIFIES two already-banked lines of absorption into ONE capstone; it closes NOTHING deeper.  No
  `sorry`, no `admit`, no `:= True`, no new axiom (`std-3` only), no vacuous / unsatisfiable
  hypothesis, no conclusion-in-disguise, no existing file edited — only NEW declarations added.
  `a₁ = R/6` stays CONDITIONAL (the `A1R6GateSlots` convergence-trio remains genuinely open).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS DOES — the union of the J4-741→748 "finish it" cycle.

  Two banked capstone lines each removed a DIFFERENT wall from the base surface:

    • `HgateOpenFlowballAbsorb.a1_R6_from_data_v4d` (J4-745) absorbs, FROM PURE GEOMETRY at ONE shared
      flow-ball gate `c`, the five semantic carriers `hgate`, `hpkgBound`, `hmemS0`, `hopenS0`, and the
      joint gate-graph measurability — all discharged internally via the augmented producer
      `hgate_flowball_width43_open`.  But it still routes its S1 (joint strong-measurability) through the
      RAW-CHART `hcarTau`/`hcarField`/`hcarField2` — the `.choose`-opacity WALL flagged by J4-747.

    • `A1R6FromDataGated.a1_R6_from_data_gated` (J4-748) ELIMINATES that raw-chart wall: its S1 is sourced
      from `GatedChartMeasAudit.tripleHEmeas_concrete_v3`, consuming a single MEASURABLE joint
      right-inverse `Gc` (`Measurable Gc`) + a GUARDED on-support agreement, in place of the opaque chart
      conjunct.  But it re-exposes the raw `hgate`/`hpkgBound`/`hmemS0`/`hopenS0` as explicit binders.

  `a1_R6_from_data_v5` COMBINES BOTH WINS.  It runs `hgate_flowball_width43_open` to obtain `a b c P₀ P₁`
  together with `hgate` + gate-openness + joint-graph measurability at ONE gate, then (verbatim as v4d)
  derives `hpkgBound` (width-2 package via the 3/2→2 chart widen), `hmemS0`, and `hopenS0` at that SAME
  gate — and feeds those directly into the GATED bundle builder
  `A1R6FromDataGated.constGate_assembly_data_from_data_gated`, whose S1 seam is the wall-free `Gc` +
  guarded-agreement route.  The bundle is fired by `FinalA1SlotsAtConstGate.fire`, the SAME firing lemma
  the gated capstone uses.

  ## NET SURFACE.  `a1_R6_from_data_v5` carries ONLY:
    • base geometry / gauge binders (`hg`,`hgsymm`,`hgiC`,`hgpos`,`hg0`,`hgi`,`hΓ`,`hdg0`,`hsrc`, and the
      producer's geometry inputs `hgnd`,`hinvF`,`hframeK`,`hw`, plus `hgiMeas`/`hchrMeas`);
    • the WALL-FREE gated jet carriers `hcarTau`/`hcarField`/`hcarField2` (`Gc`-measurability + guarded
      agreement, ∀-over-gates), together with the single joint right-inverse `Gc` + `Measurable Gc`;
    • the CONVERGENCE-TRIO `slots` (`A1R6GateSlots`, ∀-over-gates) — NEVER claimed closed;
    • the single labelled gauge carry `hGauss`.

  NO `hgate`, NO `hpkgBound`, NO `hmemS0`, NO `hopenS0` (all absorbed at the flow-ball gate).  NO
  `MeasurableSet K` binder (derived from `IsCompact K` — compact ⟹ closed ⟹ measurable).  NO group (D′) /
  `hgPull` at all — the `FinalA1SlotsAtConstGate.fire` route never uses the base-metric pullback block,
  so it is absent by construction (strictly better than shrinking group (D′) to `hgPull`).  The
  raw-chart wall is GONE.  ⚠ Still NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.A1R6FromDataGated
import QIQTH.HgateOpenFlowballAbsorb

open MeasureTheory Finset Filter Set
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.RadialTransport
open QIQTH.ParametrixFunction QIQTH.VanVleck QIQTH.HeatTransportRecursion
open QIQTH.VanVleckCancellation QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.HeatParametrixAnsatz QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.ErrorKernelFactorization
open QIQTH.DataPileWitnessAudit QIQTH.HEmeasBorelAudit QIQTH.PullbackMetric
open QIQTH.HeatKernelA1 QIQTH.ExpMap
open QIQTH.A1R6CoreAtGate QIQTH.A1R6SlotAdapters QIQTH.ConstGateAssembly QIQTH.FinalA1Slots
open QIQTH.HgateAffineRepair QIQTH.GatedRepSFix QIQTH.GatedChartMeasAudit
open QIQTH.A1R6FromData QIQTH.HGaussAbsorb QIQTH.CurvedHgateGlue
open QIQTH.HeatParametrixOrder QIQTH.GaussianPolyBound QIQTH.RNCDecay
open QIQTH.HgateOpenFlowballAbsorb QIQTH.A1R6FromDataGated
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.A1R6FromDataUnified

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ###############################################################################
    ### `a1_R6_from_data_v5` — the UNIFIED capstone (both walls removed).
    ############################################################################### -/

/-- **★★★★★ J4-749 — `a1_R6_from_data_v5`.**  The union of `HgateOpenFlowballAbsorb.a1_R6_from_data_v4d`
    (flow-ball absorption of `hgate`/`hpkgBound`/`hmemS0`/`hopenS0`/joint-measurability) and
    `A1R6FromDataGated.a1_R6_from_data_gated` (the wall-free `Gc` + guarded-agreement S1 seam).  Feeds the
    augmented flow-ball producer's outputs — all at ONE gate `c` — into the GATED bundle builder
    `constGate_assembly_data_from_data_gated`, then fires with `FinalA1SlotsAtConstGate.fire`.  Carries
    ONLY: base geometry, the wall-free gated jet carriers (+ `Gc`), the convergence-trio `slots`, and the
    gauge carry `hGauss`.  ⚠ NOT `a₁ = R/6`. -/
theorem a1_R6_from_data_v5 (hn : 1 ≤ n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    -- ── (A) base geometry / gauge binders:
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then (1 : ℝ) else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    -- ── the flow-ball producer's geometry inputs (as in v4d):
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchrMeas : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p))
    -- ── the WALL-FREE gated jet carriers (`Gc`-measurability + guarded agreement, ∀-over-gates):
    (Gc : Point n × Point n → Point n) (hGmeas : Measurable Gc)
    (hcarTau : ∀ a b c : ℝ, 0 < a → a < b → b < c →
        ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
            (chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1 ≠ 0 ∨ Cfield w.2.2 w.2.1 ≠ 0) →
            uniformInverseChart g gi hChr hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1))
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ constGate g gi hChr hK c w.2.2 ∧
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hChr hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hcarField : ∀ a b c : ℝ, 0 < a → a < b → b < c → ∀ k : Fin n,
        ∃ Pfield : Point n → Point n → Fin n → ℝ,
        (∀ jj, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 jj))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
            (chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1 ≠ 0
              ∨ pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1 ≠ 0) →
            uniformInverseChart g gi hChr hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1))
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            IsOpen (constGate g gi hChr hK c w.2.2) ∧ w.2.1 ∈ constGate g gi hChr hK c w.2.2 ∧
            (∀ jj, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update w.2.1 k s) jj)
              (Pfield w.2.2 w.2.1 jj) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1))
    (hcarField2 : ∀ a b c : ℝ, 0 < a → a < b → b < c → ∀ i j : Fin n,
        ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
        (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pjfield w.2.2 w.2.1 k))
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Qfield w.2.2 w.2.1 k))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) i w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n =>
              pd (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K →
            (chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1 ≠ 0
              ∨ pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) i w.2.1 ≠ 0
              ∨ pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j w.2.1 ≠ 0
              ∨ pd (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1 ≠ 0) →
            uniformInverseChart g gi hChr hK w.2.2 w.2.1 = Gc (w.2.2, w.2.1))
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            IsOpen (constGate g gi hChr hK c w.2.2) ∧ w.2.1 ∈ constGate g gi hChr hK c w.2.2 ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update y i s) k)
              (Pifield w.2.2 y k) (y i)) ∧
            (∀ y k, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update y j s) k)
              (Pjfield w.2.2 y k) (y j)) ∧
            (∀ k, HasDerivAt
              (fun s : ℝ => Pjfield w.2.2 (Function.update w.2.1 i s) k)
              (Qfield w.2.2 w.2.1 k) (w.2.1 i)) ∧
            (∀ y, PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) ∧
            PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) i w.2.1 ∧
            PdiffAt (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1))
    -- ── the convergence-trio slot package (∀-over-gates — NEVER claimed closed):
    (slots : ∀ a b c : ℝ, 0 < a → a < b → b < c → A1R6GateSlots g gi hChr hK c a b t)
    -- ── the single labelled gauge carry:
    (hGauss : ∀ i, (fun x => ∑ j, g x i j * x j) =ᶠ[𝓝 (0 : Point n)] (fun x => x i)) :
    ∃ a b c : ℝ, 0 < a ∧ a < b ∧ b < c ∧
    (heatOp g gi (trueHeatKernel (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))) t 0 0 = 0
    ∧ trueHeatKernel (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
        (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b))) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, ricci g gi i i 0) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)
                            (leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b)))
                            t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2)))) := by
  -- ── consume the AUGMENTED flow-ball producer: gate radii + width-4/3 `hgate` + openness + measSet.
  obtain ⟨a, b, c, P₀, P₁, ha, hab, hbc, hP₀, hP₁, hopenAll, _hKSmeasSet, hgate⟩ :=
    hgate_flowball_width43_open g gi hg hChr hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  -- ── DERIVE `hEdom` (width-3/2 Gaussian) from the SAME `hgate` at the flow-ball gate.
  obtain ⟨E₀, E₁, hE₀, hE₁, hEdom⟩ :=
    hEdom_vanVleck_of_hgate_affine g gi hChr hK (constGate g gi hChr hK c) a b P₀ P₁ hP₀ hP₁ hgate
  -- ── WIDTH-WIDEN `hEdom` (3/2 → 2) into the width-2 all-`t'` package bound `hpkgBound`.
  set S1 : ℝ := Real.sqrt (3 / 2) ^ n with hS1def
  set Sc : ℝ := Real.sqrt (2 / (3 / 2)) ^ n with hScdef
  have hS10 : (0 : ℝ) ≤ S1 := by rw [hS1def]; positivity
  have hSc0 : (0 : ℝ) ≤ Sc := by rw [hScdef]; positivity
  set C : ℝ := (E₀ + E₁) * S1 * Sc with hCdef
  have hCnn : (0 : ℝ) ≤ C := by
    rw [hCdef]; exact mul_nonneg (mul_nonneg (add_nonneg hE₀ hE₁) hS10) hSc0
  have hpkgBound : ∀ t' : ℝ, ∀ τ p q, 0 < τ → τ ≤ t' →
      |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
        ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
    intro t' τ p q hτ hτt
    have hE := hEdom τ hτ p q
    have hwiden : gaussDdim (3 / 2 * τ) (p - q) ≤ Sc * gaussDdim (2 * τ) (p - q) := by
      have hchart := gaussDdim_le_gaussDdim_chart (n := n) (c := 3 / 2) (d := 2)
        (by norm_num) (by norm_num) hτ (v := p - q) (w := p - q)
        (by nlinarith [rncRadialSq_nonneg (p - q)])
      rw [hScdef]; exact hchart
    have hbk : baseKernelW (2 : ℝ) (0 : ℝ) τ p q = gaussDdim (2 * τ) (p - q) :=
      baseKernelW_zero_apply (2 : ℝ) τ p q
    have haff : E₀ + E₁ * τ ≤ (E₀ + E₁) * (1 + t') := by nlinarith [hE₁, hE₀, hτ, hτt, hτ.le]
    have hgnn : (0 : ℝ) ≤ gaussDdim (2 * τ) (p - q) := QIQTH.ResidueBound.gaussDdim_nonneg _ _
    calc |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
          ≤ (E₀ + E₁ * τ) * S1 * gaussDdim (3 / 2 * τ) (p - q) := hE
        _ ≤ (E₀ + E₁ * τ) * S1 * (Sc * gaussDdim (2 * τ) (p - q)) := by
              apply mul_le_mul_of_nonneg_left hwiden
              exact mul_nonneg (add_nonneg hE₀ (mul_nonneg hE₁ hτ.le)) hS10
        _ = ((E₀ + E₁ * τ) * (S1 * Sc)) * gaussDdim (2 * τ) (p - q) := by ring
        _ ≤ ((E₀ + E₁) * (1 + t') * (S1 * Sc)) * gaussDdim (2 * τ) (p - q) := by
              apply mul_le_mul_of_nonneg_right _ hgnn
              apply mul_le_mul_of_nonneg_right haff
              exact mul_nonneg hS10 hSc0
        _ = (C * (1 + t')) * gaussDdim (2 * τ) (p - q) := by rw [hCdef]; ring
        _ = (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by rw [hbk]
  -- ── `hmemS0` discharged at the flow-ball gate: `φ_0 0 = 0`, `0 ∈ K`, `0 < c`.
  have hmemS0 : (0 : Point n) ∈ K → (0 : Point n) ∈ constGate g gi hChr hK c 0 := by
    intro _
    refine ⟨0, ?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_zero]; exact hc0
    · exact uniformFlowExp_zero g gi hChr hK 0 hK0
  -- ── `hopenS0` discharged at the SAME produced gate `c`, off the producer's openness export.
  have hopenS0 : (0 : Point n) ∈ K → IsOpen (constGate g gi hChr hK c 0) := by
    intro h0
    exact hopenAll 0 h0
  -- ── `MeasurableSet K` — DERIVED: compact ⟹ closed ⟹ measurable.
  have hKmeasSet : MeasurableSet K := hK.isClosed.measurableSet
  -- ── FIRE through the GATED bundle builder (wall-free `Gc` + guarded-agreement S1 seam).
  refine ⟨a, b, c, ha, hab, hbc, ?_⟩
  exact FinalA1SlotsAtConstGate.fire g gi t ht hn hChr hK hK0
    hg hgiC hgpos hg0 hgi hΓ hdg0 hsrc a b c C ha hab hbc hCnn
    (constGate_assembly_data_from_data_gated hn g gi hChr hK c a b C
      P₀ P₁ hP₀ hP₁ hgate hKmeasSet Gc hGmeas
      (hcarTau a b c ha hab hbc) (hcarField a b c ha hab hbc) (hcarField2 a b c ha hab hbc)
      hgiMeas hchrMeas hpkgBound hmemS0 hopenS0)
    (finalA1Slots_from_data g gi hChr hK c a b t (slots a b c ha hab hbc)
      hg hgsymm hgiC hgi hdg0 hGauss)

end QIQTH.A1R6FromDataUnified

/-! ## Axiom check — the unified capstone is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.A1R6FromDataUnified
#print axioms a1_R6_from_data_v5
end AxiomChecks
