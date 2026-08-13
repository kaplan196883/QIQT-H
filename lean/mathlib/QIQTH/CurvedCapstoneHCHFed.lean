/-
  CurvedCapstoneHCHFed — J4-669: the CURVED trunc `a₁` capstone with BOTH the Duhamel per-step
  integrability slot `hInt` (J4-668) AND the spatial-`C²` witness slot `hCH` FED FROM GEOMETRY.
  ONE brick of the `a₁ = R/6` heat-kernel campaign.  NOT `a₁ = R/6`; proves NOTHING new about `R/6`
  (R/6 stays a labelled carrier; gaps (ii)–(v) minus `hCH` untouched).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL — ONE MORE ARROW DISCHARGED, NOTHING ELSE.  This file takes the J4-668 curved
  capstone `CurvedCapstoneGateUnify.curved_wide_a1_R6_trunc_hIntFed` (which carried the FIVE inner
  Duhamel arrows `hDuhamel`/`hInter`/`hDConv`/`hCH`/`hCConv`) and additionally discharges `hCH` — the
  spatial second-jet of the gated van-Vleck witness — FROM GEOMETRY, shortening the returned
  implication's inner-arrow list to FOUR (`hDuhamel`/`hInter`/`hDConv`/`hCConv`).  It closes NOTHING of
  the `R/6` coefficient extraction.  The labelled inputs `hw`/`hu`/`hsrc` and the jet-reach antecedent
  remain.

  ── THE `hCH` DISCHARGE (route = direct geometry supplier at the constant-radius gate).
     The banked flat/abstract supplier `InftyRebaseCapstone.hCH_discharge_from_geometry` produces
     EXACTLY the arrow shape `ContDiffAt ℝ 2 (fun p => vanVleckGatedWitness g gi hChr hK S a b t p 0) 0`
     from `{hK0, hS0, hSopen, hg, hgi, hgpos, hg0}` — pure geometry.  At the genuinely-curved witness
     `(g,gi) := (curvedRNCMetric κ, curvedRNCInv κ)` (`κ < 0`), gate `S := constGate … c` (seed
     `K = {0}`), every input is discharged from a BANKED curved supplier:
       • `hK0`   ⟸ `Set.mem_singleton 0`;
       • `hS0`   ⟸ `CurvedA1ClassB.curved_hmemS0_at_gate_of_lt` (the SAME supplier the J4-668 capstone
                    uses for its `hS0` gate input);
       • `hSopen`⟸ `CurvedA1ClassBMeas2.curved_hopenS0_at_gate` (concrete flow-ball gate openness,
                    geometry-only floor `flowBall_gateRadius_floor`), under the gate-smallness `c < c₀`;
       • `hg`    ⟸ `CurvedRNCGaussWitness.curvedRNCMetric_contDiff`;
       • `hgi`   ⟸ `CurvedRNCGaugeBundle.curvedRNCInv_contDiff` (`κ ≤ 0`);
       • `hgpos` ⟸ `CurvedRNCPosDef.curvedRNCMetric_hgpos` (`κ ≤ 0`; det `g^K > 0` via PosDef);
       • `hg0`   ⟸ `curvedRNCMetric_zero` (gauge-centre `g^K(0) = δ`).
     The openness reach `c₀` (geometry-only, from `hChr`+`hK`) is FOLDED into the returned jet reach:
     the capstone now returns `min δ₀ c₀` in place of `δ₀`, so the SINGLE gate-smallness antecedent
     `c < min δ₀ c₀` delivers BOTH `c < δ₀` (the S1 surface) and `c < c₀` (gate openness).  No new
     antecedent axis is added; the existing `c < δ₀` reach is merely tightened.

  ── HONEST RESIDUE of `curved_wide_a1_R6_trunc_hIntCHFed` (the returned implication's antecedents):
       • the jet-reach smallness `c < min δ₀ c₀`  (jet reach ∧ gate-openness reach, geometry-only);
       • the LABELLED geometric inputs `hw` (amplitude `C^∞`), `hu` (transport-coeff `C^∞`),
         `hsrc` (SDW transport regularity);
       • the FOUR remaining Duhamel arrows `hDuhamel`/`hInter`/`hDConv`/`hCConv` (gaps (ii)–(v) minus
         `hCH`, carried as inner hypotheses — satisfiable interface facts, never the conclusion).
     Every one is satisfiable, non-vacuous, at a GENUINELY-CURVED witness (`κ < 0`, `Ric(0) =
     (n−1)κ δ ≠ 0`), and NONE is `a₁ = R/6`.

  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypotheses.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CurvedCapstoneGateUnify
import QIQTH.InftyRebaseCapstone
import QIQTH.CurvedA1ClassBMeas2
import QIQTH.CurvedRNCPosDef

open MeasureTheory
open QIQTH.Curvature QIQTH.TrueHeatKernel QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant
open QIQTH.TruncatedHIntRethread QIQTH.HEmeasBorelAudit
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedA1CenterAmp
open QIQTH.A1R6CoreAtGate QIQTH.CurvedRNCHeatOpDomPkg QIQTH.CurvedA1GateS1
open QIQTH.GaussGaugeToHgauge QIQTH.CurvedA1ClassB QIQTH.ResidualFactorization
open QIQTH.WideA1AssemblyTrunc QIQTH.TruncHIntFromGeometry
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.CurvedCapstoneGateUnify QIQTH.InftyRebaseCapstone QIQTH.CurvedA1ClassBMeas2
open QIQTH.CurvedRNCPosDef
open scoped BigOperators Topology ContDiff

namespace QIQTH.CurvedCapstoneHCHFed

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ###############################################################################
    ### THE CURVED CAPSTONE with `hInt` AND `hCH` fed from geometry (gate = `constGate … c`).
    ############################################################################### -/

/-- **★★★★ J4-669 — `curved_wide_a1_R6_trunc_hIntCHFed`.**  The J4-668 curved trunc `a₁` capstone
    `CurvedCapstoneGateUnify.curved_wide_a1_R6_trunc_hIntFed` with the spatial-`C²` witness slot `hCH`
    ADDITIONALLY discharged from geometry via `InftyRebaseCapstone.hCH_discharge_from_geometry` at the
    constant-radius gate `constGate … c` (seed `K = {0}`), using the banked curved gauge suppliers.
    The returned implication's inner-arrow list is therefore SHORTER by exactly the `hCH` arrow:
    `hDuhamel`/`hInter`/`hDConv`/`hCConv` remain.  The jet reach is tightened to `min δ₀ c₀` (S1 surface
    reach ∧ gate-openness reach), keeping a SINGLE gate-smallness antecedent.

    HONEST RESIDUE (all satisfiable, non-vacuous, never the conclusion, NEVER `a₁ = R/6`):
      • the jet-reach antecedent `c < min δ₀ c₀`;
      • the LABELLED geometric inputs `hw`/`hu`/`hsrc`;
      • the remaining Duhamel arrows `hDuhamel`/`hInter`/`hDConv`/`hCConv`, carried as INNER hypotheses.
    ⚠ NOT `a₁ = R/6`. -/
theorem curved_wide_a1_R6_trunc_hIntCHFed (κ : ℝ) (hκneg : κ < 0) (hn : 1 ≤ n)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric κ))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
          (curvedRNCMetric κ) (curvedRNCInv κ))) k : Point n → ℝ))
    (hu : ∀ k : ℕ, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck (curvedRNCMetric (n := n) κ)) (curvedRNCMetric κ)
        (curvedRNCInv κ)) k))
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck (curvedRNCMetric (n := n) κ)) (curvedRNCMetric κ) (curvedRNCInv κ)
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ)) (curvedRNCMetric κ)
          (curvedRNCInv κ)) 0)))
    (T₀ : ℝ) (hT₀ : 0 < T₀) :
    ∃ a b C c : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ b < c ∧
      ∃ δ₀ > (0 : ℝ), c < δ₀ →
        -- ── the remaining Duhamel arrows (gaps (ii)–(v) minus `hCH`), carried as INNER hypotheses ──
        (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
              (fun u p q => heatConv (cW (n := n) κ hκneg a b c)
                (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c))) u p q)
              T₀ 0 0
            = leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c)) T₀ 0 0
              + heatConv (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c))
                  (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c))) T₀ 0 0) →
        (heatConv (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c))
              (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c))) T₀ 0 0
            = ∑' k : ℕ, heatConv (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c))
                (fun τ p q => (-1 : ℝ) ^ (k + 1)
                  * iterE (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c)) (k + 1) τ p q)
                T₀ 0 0) →
        DifferentiableAt ℝ (fun u => heatConv (cW (n := n) κ hκneg a b c)
            (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c))) u 0 0) T₀ →
        ContDiffAt ℝ 2 (fun p => heatConv (cW (n := n) κ hκneg a b c)
            (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c))) T₀ p 0)
            (0 : Point n) →
        -- ── the a₁ two-jet conclusion at the curved witness ──
        heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
            (trueHeatKernel (cW (n := n) κ hκneg a b c)
              (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c)))) T₀ 0 0 = 0
        ∧ trueHeatKernel (cW (n := n) κ hκneg a b c)
            (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c))) T₀ 0 0
            = (QIQTH.HeatKernelA1.heatKernel1D T₀ 0) ^ n
              * (1 + ((∑ i, ricci (curvedRNCMetric κ) (flatMetric n) i i 0) / 6) * T₀
                  + T₀ ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                              transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
                                (curvedRNCMetric κ) (curvedRNCInv κ)) k (0 : Point n)
                                * T₀ ^ (k - 2))
                            + heatConv (cW (n := n) κ hκneg a b c)
                                (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                                  (cW (n := n) κ hκneg a b c))) T₀ 0 0
                                / ((QIQTH.HeatKernelA1.heatKernel1D T₀ 0) ^ n * T₀ ^ 2))) := by
  -- ── the ONE curved provider: gate `(a,b,c)`, constant `C`, the all-t' width-2 defect bound. ──
  obtain ⟨a, b, C, c, ha, hab, hCnn, hbc, hpkgBound, _hAdom⟩ :=
    curvedRNC_heatOp_dom_pkg κ hκneg (curvedRNC_hChr κ hκneg.le) hw T₀
  -- ── the S1 (`tripleHEmeas`) surface at the SAME `(a,b,c)` gate (jet reach `δ₀`). ──
  obtain ⟨δ₀, hδ₀, hS1⟩ :=
    curved_hS1_at_gate κ hκneg (by omega : 0 < n) (curvedRNC_hChr κ hκneg.le)
      (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) a b c ha hab hbc hu
  -- ── the gate-openness reach `c₀` (geometry-only: `hChr` + `hK`). ──
  obtain ⟨c₀, hc₀, hopenSpec⟩ :=
    curved_hopenS0_at_gate κ (curvedRNC_hChr κ hκneg.le)
      (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
  refine ⟨a, b, C * (1 + T₀), c, ha, hab, mul_nonneg hCnn (by linarith), hbc,
    min δ₀ c₀, lt_min hδ₀ hc₀, fun hcδ => ?_⟩
  intro hDuhamel hInter hDConv hCConv
  have hcδ0 : c < δ₀ := lt_of_lt_of_le hcδ (min_le_left _ _)
  have hcc0 : c < c₀ := lt_of_lt_of_le hcδ (min_le_right _ _)
  have hcpos : 0 < c := by linarith
  -- ── `hInt` from the curved closure internals: affine slice `hAff` + S1 surface `hEmeas`. ──
  have hAff : ∀ τ p q, 0 < τ → τ ≤ T₀ →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c) τ p q|
        ≤ C * (1 + τ) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
    intro τ p q hτ _
    exact hpkgBound τ τ p q hτ le_rfl
  have hEmeas := hS1 hcδ0
  have hInt : IterConvIntegrableWOn
      (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c)) 2 (0 : ℝ) (C * (1 + T₀)) T₀ :=
    hIntOn_affine_from_geometry (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκneg.le)
      (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
      (constGate (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκneg.le)
        (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) c) a b hn
      (2 : ℝ) C T₀ (by norm_num) hCnn hAff hEmeas
  -- ── `hEboundW_le` from the SAME `hpkgBound` at cutoff `t' := T₀` (fixed-constant width-2 form). ──
  have hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ T₀ →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c) τ p q|
        ≤ (C * (1 + T₀)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
    intro τ p q hτ hτT
    exact hpkgBound T₀ τ p q hτ hτT
  -- ── the banked curved gauge binders. ──
  have hg0' : ∀ i j, curvedRNCMetric κ (0 : Point n) i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    intro i j; rw [curvedRNCMetric_zero κ i j, Matrix.one_apply]
  -- ── `hCH` (spatial `C²` of the gated van-Vleck witness) fed from geometry. ──
  have hSopen : IsOpen (constGate (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκneg.le)
      (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) c 0) :=
    hopenSpec c hcpos hcc0 (Set.mem_singleton (0 : Point n))
  have hCH : ContDiffAt ℝ 2 (fun p => cW (n := n) κ hκneg a b c T₀ p 0) (0 : Point n) :=
    hCH_discharge_from_geometry (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκneg.le)
      (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
      (constGate (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκneg.le)
        (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) c) a b T₀
      (Set.mem_singleton (0 : Point n))
      (curved_hmemS0_at_gate_of_lt κ (curvedRNC_hChr κ hκneg.le)
        (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) a b c ha hab hbc
        (Set.mem_singleton (0 : Point n)))
      hSopen
      (fun a' b' => curvedRNCMetric_contDiff κ a' b')
      (fun a' b' => curvedRNCInv_contDiff κ hκneg.le a' b')
      (curvedRNCMetric_hgpos κ hκneg.le) hg0'
  -- ── thread the explicit-gate trunc capstone at `S := constGate … c`, `hCH` now supplied. ──
  exact wide_a1_R6_of_residue_inf_trunc (curvedRNCMetric κ) (curvedRNCInv κ)
    (fun cc d => ricci (curvedRNCMetric κ) (flatMetric n) cc d 0) T₀ hT₀ (C * (1 + T₀))
    (mul_nonneg hCnn (by linarith)) (2 : ℝ) (by norm_num) (curvedRNC_hChr κ hκneg.le)
    (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκneg.le)
      (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) c) a b ha hab
    (Set.mem_singleton (0 : Point n))
    (curved_hmemS0_at_gate_of_lt κ (curvedRNC_hChr κ hκneg.le)
      (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) a b c ha hab hbc
      (Set.mem_singleton (0 : Point n)))
    (cW (n := n) κ hκneg a b c) rfl
    (fun a' b' => curvedRNCMetric_contDiff κ a' b') hg0'
    (fun i j => curvedRNCInv_zero κ i j)
    (fun k i j => curvedRNCMetric_christoffel_zero κ k i j)
    (fun a' b' e => curvedRNCMetric_pd_zero κ a' b' e)
    (fun cc d => curvedRNCMetric_htr_from_gauge κ cc d) hsrc
    hEboundW_le hInt hDuhamel hInter hDConv hCH hCConv

/-! ###############################################################################
    ### NON-VACUITY — the capstone lives at a GENUINELY-CURVED witness (`κ ≠ 0`, `n ≥ 2`).
    ############################################################################### -/

/-- **★ J4-669 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  The witness underlying
    `curved_wide_a1_R6_trunc_hIntCHFed` is genuinely curved: for `κ ≠ 0`, `n ≥ 2` the diagonal
    metric-Hessian trace (`Ric(0)`) of `curvedRNCMetric κ` is nonzero.  Re-exports
    `CurvedCapstoneGateUnify.curved_wide_a1_R6_trunc_hIntFed_curved_satisfiable`.  NOT `a₁ = R/6`. -/
theorem curved_wide_a1_R6_trunc_hIntCHFed_curved_satisfiable
    (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curved_wide_a1_R6_trunc_hIntFed_curved_satisfiable κ hκ hn c

end QIQTH.CurvedCapstoneHCHFed

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CurvedCapstoneHCHFed
#print axioms curved_wide_a1_R6_trunc_hIntCHFed
#print axioms curved_wide_a1_R6_trunc_hIntCHFed_curved_satisfiable
end AxiomChecks
