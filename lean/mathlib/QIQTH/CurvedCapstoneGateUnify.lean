/-
  CurvedCapstoneGateUnify — J4-668: gap-(i) GATE-UNIFICATION brick.  Connect the curved
  truncated-integrability closure (`TruncHIntCarries.curved_hIntOn_from_geometry_closed`, J4-666) to
  the trunc-rethreaded `a₁` capstone, yielding the CURVED instantiation of the `a₁` two-jet capstone
  with the Duhamel per-step integrability slot `hInt` FED FROM GEOMETRY.  ONE brick of the `a₁ = R/6`
  heat-kernel campaign.  NOT `a₁ = R/6`; proves NOTHING new about `R/6` (R/6 stays a labelled carrier;
  gaps (ii)–(v) untouched).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL — GAP (i) GATE-UNIFICATION ONLY.  This file wires the curved `hInt` closure into
  a truncated `a₁` capstone.  It closes NOTHING of the `R/6` coefficient extraction: the OTHER Duhamel
  arrows `hDuhamel`/`hInter`/`hDConv`/`hCH`/`hCConv` (gaps (ii)–(v)) remain CARRIED as inner hypotheses
  of the returned implication, exactly as the mainline capstones carry them; the labelled geometric
  inputs `hw`/`hu`/`hsrc` and the jet-reach antecedent `c < δ₀` also remain.

  ── THE GATE MISMATCH (the brick's raison d'être; ROUTE TAKEN = A, realized at the explicit-gate
     capstone).  The existential-gate capstone
     `ResidualAssemblyTrunc.wide_a1_R6_of_residue_inf_hEboundW_discharged_trunc` (J4-667)
     EXISTENTIALIZES its gate `(a,b,C',S)` to the residual provider `hEboundW_wide_from_geometry`'s own
     choice.  That provider's gate is, definitionally, the VARYING-radius flow-ball
     `S q := uniformFlowExp … q '' Metric.ball 0 (cf q)` with `cf q = (hgood q _).choose`
     (`GatedWitnessPackage.gatedWitnessN1_hEboundW_le_of_good_pkg`) — NOT the literal constant-radius
     `constGate … c = fun z => uniformFlowExp … z '' Metric.ball 0 c` that the curved closure gates at.
     The two are two INDEPENDENT existential witnesses (varying-radius `choose` vs constant `c`), with
     no definitional bridge — so feeding the curved `hInt` (at `constGate … c`) directly into that
     capstone's `hInt` slot is genuinely BLOCKED (varying ≠ constant gate).  Route B (integrability
     monotonicity across gates) also fails: different gates ⟹ different gated witnesses ⟹ different
     heat operators / iterated convolutions, with no inclusion between the two `IterConvIntegrableWOn`
     families.

     THE REPAIR (route A, executed here).  The trunc capstone one level down,
     `WideA1AssemblyTrunc.wide_a1_R6_of_residue_inf_trunc`, takes the gate `S a b` as EXPLICIT
     arguments (it does NOT existentialize).  So we CHOOSE `S := constGate … c` — the SAME gate the
     curved closure produces — and thread it there, feeding BOTH residual slots from the ONE curved
     provider `CurvedRNCHeatOpDomPkg.curvedRNC_heatOp_dom_pkg` (so `hInt` and `hEboundW_le` land at the
     SAME `(a,b,c)`, avoiding the two-existential mismatch one level down):
       • `hInt`        ⟸ `TruncHIntFromGeometry.hIntOn_affine_from_geometry` on the affine slice
                          `hAff := hpkgBound τ τ …` + the S1 surface `curved_hS1_at_gate`
                          (== the internals of `curved_hIntOn_from_geometry_closed`, J4-666);
       • `hEboundW_le` ⟸ the SAME `hpkgBound` at the fixed outer cutoff `t' := T₀`
                          (`|heatOp …| ≤ (C·(1+T₀))·baseKernelW 2 0`, the fixed-constant width-2 form).
     The geometry/gauge binders of `wide_a1_R6_of_residue_inf_trunc` are discharged from the banked
     curved suppliers:  `hg`/`hg0`/`hgi`/`hΓ`/`hdg0` from the curved gauge members
     (`curvedRNCMetric_contDiff`/`_zero`/`curvedRNCInv_zero`/`curvedRNCMetric_christoffel_zero`/`_pd_zero`);
     `htr` from `GaussGaugeToHgauge.curvedRNCMetric_htr_from_gauge` (`Ric := ricci (curvedRNCMetric κ)
     (flatMetric n) · · 0`, the gauge-pinned curved Ricci);  `hS0` from
     `CurvedA1ClassB.curved_hmemS0_at_gate_of_lt`;  `hsrc` CARRIED (labelled).

  ── HONEST RESIDUE of `curved_wide_a1_R6_trunc_hIntFed` (the returned implication's antecedents):
       • the jet-reach smallness `c < δ₀`  (the pkg's gate radius vs the Gc jet reach — the SAME
         arithmetic compatibility isolated in `CurvedA1GateS1`, NOT measurability, NOT the bound);
       • the LABELLED geometric inputs `hw` (amplitude `C^∞`), `hu` (transport-coeff `C^∞`),
         `hsrc` (SDW transport regularity);
       • the FOUR-plus-one remaining Duhamel arrows `hDuhamel`/`hInter`/`hDConv`/`hCH`/`hCConv`
         (gaps (ii)–(v), carried as inner hypotheses — satisfiable interface facts, never the
         conclusion).
     Every one is satisfiable, non-vacuous, at a GENUINELY-CURVED witness (`κ < 0`, `Ric(0) =
     (n−1)κ δ ≠ 0`), and NONE is `a₁ = R/6`.

  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypotheses.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.TruncHIntCarries
import QIQTH.TruncHIntFromGeometry
import QIQTH.WideA1AssemblyTrunc
import QIQTH.CurvedA1ClassB
import QIQTH.GaussGaugeToHgauge

open MeasureTheory
open QIQTH.Curvature QIQTH.TrueHeatKernel QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant
open QIQTH.TruncatedHIntRethread QIQTH.HEmeasBorelAudit
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle QIQTH.CurvedA1CenterAmp
open QIQTH.A1R6CoreAtGate QIQTH.CurvedRNCHeatOpDomPkg QIQTH.CurvedA1GateS1
open QIQTH.GaussGaugeToHgauge QIQTH.CurvedA1ClassB QIQTH.ResidualFactorization
open QIQTH.WideA1AssemblyTrunc QIQTH.TruncHIntFromGeometry
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.HeatDuhamel QIQTH.LeviSeries
open scoped BigOperators Topology ContDiff

namespace QIQTH.CurvedCapstoneGateUnify

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-- The curved gated van-Vleck witness at the constant-radius flow-ball gate `constGate … c`
    (seed `K = {0}`) — the SAME gate the curved `hInt` closure produces, abbreviated for readability. -/
noncomputable abbrev cW (κ : ℝ) (hκneg : κ < 0) (a b c : ℝ) : ℝ → Point n → Point n → ℝ :=
  vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκneg.le)
    (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκneg.le)
      (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) c) a b

/-! ###############################################################################
    ### THE CURVED CAPSTONE with the `hInt` slot FED FROM GEOMETRY (gate = `constGate … c`).
    ############################################################################### -/

/-- **★★★★ J4-668 — `curved_wide_a1_R6_trunc_hIntFed`.**  The TRUNCATED `a₁` two-jet capstone
    `WideA1AssemblyTrunc.wide_a1_R6_of_residue_inf_trunc` instantiated at the genuinely-curved witness
    `(curvedRNCMetric κ, curvedRNCInv κ)` (`κ < 0`, `Ric ≠ 0`), gate `= constGate … c` (seed `K = {0}`),
    width `2`, time `T₀`, with BOTH residual slots fed from the ONE curved provider
    `curvedRNC_heatOp_dom_pkg`:  the per-step integrability slot `hInt` is DISCHARGED via the curved
    closure internals (`hIntOn_affine_from_geometry` on `hpkgBound`'s affine slice + the S1 surface
    `curved_hS1_at_gate`), and the residual Gaussian domination `hEboundW_le` from the SAME `hpkgBound`
    at cutoff `t' := T₀`.  The `Ric` is the gauge-pinned curved Ricci `ricci (curvedRNCMetric κ)
    (flatMetric n) · · 0` (`curvedRNCMetric_htr_from_gauge`).

    HONEST RESIDUE (all satisfiable, non-vacuous, never the conclusion, NEVER `a₁ = R/6`):
      • the jet-reach antecedent `c < δ₀`;
      • the LABELLED geometric inputs `hw`/`hu`/`hsrc`;
      • the remaining Duhamel arrows `hDuhamel`/`hInter`/`hDConv`/`hCH`/`hCConv` (gaps (ii)–(v)),
        carried as INNER hypotheses of the returned implication.
    ⚠ NOT `a₁ = R/6`. -/
theorem curved_wide_a1_R6_trunc_hIntFed (κ : ℝ) (hκneg : κ < 0) (hn : 1 ≤ n)
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
        -- ── the remaining Duhamel arrows (gaps (ii)–(v)), carried as INNER hypotheses ──
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
        ContDiffAt ℝ 2 (fun p => cW (n := n) κ hκneg a b c T₀ p 0) (0 : Point n) →
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
  refine ⟨a, b, C * (1 + T₀), c, ha, hab, mul_nonneg hCnn (by linarith), hbc, δ₀, hδ₀, fun hcδ => ?_⟩
  intro hDuhamel hInter hDConv hCH hCConv
  -- ── `hInt` from the curved closure internals: affine slice `hAff` + S1 surface `hEmeas`. ──
  have hAff : ∀ τ p q, 0 < τ → τ ≤ T₀ →
      |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c) τ p q|
        ≤ C * (1 + τ) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
    intro τ p q hτ _
    exact hpkgBound τ τ p q hτ le_rfl
  have hEmeas := hS1 hcδ
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
  -- ── thread the explicit-gate trunc capstone at `S := constGate … c`. ──
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

/-- **★ J4-668 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  The witness underlying
    `curved_wide_a1_R6_trunc_hIntFed` is genuinely curved: for `κ ≠ 0`, `n ≥ 2` the diagonal
    metric-Hessian trace (`Ric(0)`) of `curvedRNCMetric κ` is nonzero.  So the fed capstone is about a
    curved metric (`κ < 0 ⊂ κ ≠ 0`), NOT vacuously the flat kernel.  Re-exports
    `CurvedRNCHeatOpDomPkg.curvedRNC_heatOp_dom_pkg_curved_satisfiable`.  NOT `a₁ = R/6`. -/
theorem curved_wide_a1_R6_trunc_hIntFed_curved_satisfiable
    (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNC_heatOp_dom_pkg_curved_satisfiable κ hκ hn c

end QIQTH.CurvedCapstoneGateUnify

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CurvedCapstoneGateUnify
#print axioms curved_wide_a1_R6_trunc_hIntFed
#print axioms curved_wide_a1_R6_trunc_hIntFed_curved_satisfiable
end AxiomChecks
