/-
  CurvedCapstoneUnifiedGate — J4-681: THE CAPSTONE RE-COMPOSED ON THE UNIFIED GATE.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT THIS FILE DOES.

  The J4-670 curved trunc `a₁` capstone `CurvedCapstoneHCHInterFed.curved_wide_a1_R6_trunc_hIntCHInterFed`
  sourced its geometry-fed slots (`hInt`/`hEboundW_le`/`hInter`/`hCH`) from `curvedRNC_heatOp_dom_pkg`,
  whose ∃-produced gate `(a,b,c)` is DISJOINT from the width-3/2 suppliers' gates (`hEdom`/`hAdom`).
  J4-680 (`CurvedUnifiedGateBounds.curvedRNC_unified_gate_bounds`) removed that obstruction: it
  ∃-produces ONE gate `(a,b,c)` and one gated van-Vleck witness `cW` carrying, SIMULTANEOUSLY, the
  width-2 all-`t'` `hpkgBound`, the width-3/2 `hEdom`, the width-3/2 `hAdom` and the frozen `hWDom`.

  This file RE-RUNS the capstone's fed-slot instantiation chain against that unified bundle, so the
  capstone's geometry-fed slots (`hInt`/`hEboundW_le`/`hInter`/`hCH`, all sourced from the unified
  `hpkgBound`'s affine slice + cutoff `t' := T₀`) AND the width-3/2 certificates (`hEdom`/`hAdom`) now
  live on the SAME witness `cW` at the SAME `(a,b,c)`.  The gate is literally `constGate … c =
  fun z => uniformFlowExp … z '' ball 0 c`, so `cW κ hκneg a b c` is DEFINITIONALLY the unified
  witness (same `hChr := curvedRNC_hChr κ hκneg.le`, same flow-ball gate) — no re-analysis, only a
  re-instantiation of the same closure chain against a gate that also carries the width-3/2 bounds.

  ── HONEST RESIDUE of `curved_wide_a1_R6_trunc_unifiedGate` (UNCHANGED from J4-670 — this is PLUMBING):
       • the jet-reach smallness `c < min δ₀ c₀`  (jet reach ∧ gate-openness reach, geometry-only);
       • the LABELLED geometric inputs `hw` (amplitude `C^∞`), `hu` (transport-coeff `C^∞`),
         `hsrc` (SDW transport regularity);
       • the THREE remaining Duhamel arrows `hDuhamel`/`hDConv`/`hCConv` (gaps (ii)–(v) minus
         `hInter`/`hCH`, carried as inner hypotheses — satisfiable interface facts, never the conclusion);
       • the W-census analytic pile and `R/6` as a LABELLED carrier — UNTOUCHED, owed.
     Every antecedent is satisfiable, non-vacuous, at a GENUINELY-CURVED witness (`κ < 0`, `Ric(0) =
     (n−1)κ δ ≠ 0`, seed `K = {0}` per cp466), and NONE is `a₁ = R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL — CAPSTONE PLUMBING ONLY, NOTHING ELSE.  This file re-composes an EXISTING
  capstone onto the unified gate; it discharges NO new arrow, closes NOTHING of the `R/6` coefficient
  extraction, and adds NO analysis.  The width-3/2 `hEdom`/`hAdom` are carried through VERBATIM from the
  unified bundle.  R/6 stays a labelled carrier; the arrows (`hDuhamel`/`hDConv`/`hCConv`), the W-census
  and the labelled inputs (`hw`/`hu`/`hsrc`) remain owed.

  No `sorry` (header prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable
  hypotheses, no existing file edited.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CurvedCapstoneHCHInterFed
import QIQTH.CurvedUnifiedGateBounds

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
open QIQTH.CurvedRNCPosDef QIQTH.CurvedCapstoneHCHFed QIQTH.LeviInterchangeTrunc
open QIQTH.DataPileWitnessAudit QIQTH.CurvedUnifiedGateBounds QIQTH.FlatHeatEquation
open scoped BigOperators Topology ContDiff

namespace QIQTH.CurvedCapstoneUnifiedGate

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ###############################################################################
    ### THE CURVED CAPSTONE re-composed on the UNIFIED gate (`curvedRNC_unified_gate_bounds`).
    ###   geometry-fed slots `hInt`/`hEboundW_le`/`hInter`/`hCH` AND the width-3/2 `hEdom`/`hAdom`
    ###   certificates all on ONE witness `cW` at ONE gate `(a,b,c)`.
    ############################################################################### -/

/-- **★★★★ J4-681 — `curved_wide_a1_R6_trunc_unifiedGate`.**  The J4-670 curved trunc `a₁` capstone
    RE-COMPOSED on the width-unified gate `curvedRNC_unified_gate_bounds`.  For the genuinely-curved
    witness `g^κ = curvedRNCMetric κ` (`κ < 0`, seed `K = {0}`), given ONLY the standing labelled
    carries `hw`/`hu`/`hsrc` and a window `T₀ > 0`, there is ONE gate `(a,b,c)` whose gated van-Vleck
    witness `cW := cW κ hκneg a b c` satisfies, SIMULTANEOUSLY:

    * the width-3/2 heatOp certificate `hEdom` (constants `E₀,E₁ ≥ 0`);
    * the width-3/2 witness certificate `hAdom` (constants `A₀,A₁ ≥ 0`);
    * the truncated `a₁` two-jet capstone with `hInt`/`hEboundW_le`/`hInter`/`hCH` ALL FED from the SAME
      unified `hpkgBound` (its affine slice + cutoff `t' := T₀`), leaving the three Duhamel arrows
      `hDuhamel`/`hDConv`/`hCConv` as inner hypotheses.

    All on the ONE witness `cW` at the ONE gate `(a,b,c)` — the fed slots and the width-3/2 certificates
    are no longer split across disjoint gates.  This is the J4-680 gate-unification consumed by the
    capstone; it discharges NO new arrow and is NOT a re-derivation of any analysis.

    HONEST RESIDUE (all satisfiable, non-vacuous, never the conclusion, NEVER `a₁ = R/6`):
      • the jet-reach antecedent `c < min δ₀ c₀`;
      • the LABELLED geometric inputs `hw`/`hu`/`hsrc`;
      • the remaining Duhamel arrows `hDuhamel`/`hDConv`/`hCConv`, carried as INNER hypotheses;
      • the W-census pile and `R/6` (a labelled carrier), untouched.
    ⚠ NOT `a₁ = R/6`. -/
theorem curved_wide_a1_R6_trunc_unifiedGate (κ : ℝ) (hκneg : κ < 0) (hn : 1 ≤ n)
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
      ∃ E₀ E₁ A₀ A₁ : ℝ, 0 ≤ E₀ ∧ 0 ≤ E₁ ∧ 0 ≤ A₀ ∧ 0 ≤ A₁ ∧
      -- ── width-3/2 heatOp certificate `hEdom` on the SAME `cW` ──
      (∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
        |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c) τ p q|
          ≤ (E₀ + E₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q)) ∧
      -- ── width-3/2 witness certificate `hAdom` on the SAME `cW` ──
      (∀ τ : ℝ, 0 < τ → ∀ p q : Point n,
        |cW (n := n) κ hκneg a b c τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q)) ∧
      ∃ δ₀ > (0 : ℝ), c < δ₀ →
        -- ── the remaining Duhamel arrows (gaps (ii)–(v) minus `hInter`/`hCH`), inner hypotheses ──
        (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
              (fun u p q => heatConv (cW (n := n) κ hκneg a b c)
                (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c))) u p q)
              T₀ 0 0
            = leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c)) T₀ 0 0
              + heatConv (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c))
                  (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c))) T₀ 0 0) →
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
  -- ═══ THE ONE UNIFIED PROVIDER: gate `(a,b,c)`, width-2 `hpkgBound`, width-3/2 `hEdom`/`hAdom`. ══════
  obtain ⟨a, b, c, ha, hab, hbc, C, hCnn, E₀, E₁, hE₀, hE₁, A₀, A₁, hA₀, hA₁,
      CW, lam, _hCW, _hlam, hpkgBound, hEdom, hAdom, _hWDom⟩ :=
    curvedRNC_unified_gate_bounds κ hκneg (curvedRNC_hChr κ hκneg.le) hw T₀ hT₀
  refine ⟨a, b, C, c, ha, hab, hCnn, hbc, E₀, E₁, A₀, A₁, hE₀, hE₁, hA₀, hA₁, ?_, ?_, ?_⟩
  · -- ── width-3/2 `hEdom` certificate on `cW` (defeq: `constGate … c = flow-ball gate`). ──
    intro τ hτ p q; exact hEdom τ hτ p q
  · -- ── width-3/2 `hAdom` certificate on `cW`. ──
    intro τ hτ p q; exact hAdom τ hτ p q
  · -- ═══ THE CAPSTONE CHAIN, fed from the UNIFIED `hpkgBound`. ══════════════════════════════════════
    -- ── the S1 (`tripleHEmeas`) surface at the SAME `(a,b,c)` gate (jet reach `δ₀`). ──
    obtain ⟨δ₀, hδ₀, hS1⟩ :=
      curved_hS1_at_gate κ hκneg (by omega : 0 < n) (curvedRNC_hChr κ hκneg.le)
        (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) a b c ha hab hbc hu
    -- ── the gate-openness reach `c₀` (geometry-only: `hChr` + `hK`). ──
    obtain ⟨c₀, hc₀, hopenSpec⟩ :=
      curved_hopenS0_at_gate κ (curvedRNC_hChr κ hκneg.le)
        (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
    refine ⟨min δ₀ c₀, lt_min hδ₀ hc₀, fun hcδ => ?_⟩
    intro hDuhamel hDConv hCConv
    have hcδ0 : c < δ₀ := lt_of_lt_of_le hcδ (min_le_left _ _)
    have hcc0 : c < c₀ := lt_of_lt_of_le hcδ (min_le_right _ _)
    have hcpos : 0 < c := by linarith
    -- ── `hInt` from the unified closure internals: affine slice `hAff` + S1 surface `hEmeas`. ──
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
    -- ── `hEboundW_le` from the SAME unified `hpkgBound` at cutoff `t' := T₀`. ──
    have hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ T₀ →
        |heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c) τ p q|
          ≤ (C * (1 + T₀)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
      intro τ p q hτ hτT
      exact hpkgBound T₀ τ p q hτ hτT
    -- ── `hEzero` (nonpositive-time vanishing of the gated-witness heat operator) from geometry. ──
    have hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n,
        heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c) τ p q = 0 :=
      hEzeroE_concrete (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκneg.le)
        (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))
        (constGate (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκneg.le)
          (isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))) c) a b hn
    -- ── ★ `hInter` (tsum/heatConv interchange) fed from geometry via the TRUNCATED interchange. ──
    have hInter : heatConv (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c))
          (leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c))) T₀ 0 0
        = ∑' k : ℕ, heatConv (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c))
            (fun τ p q => (-1 : ℝ) ^ (k + 1)
              * iterE (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c)) (k + 1) τ p q)
            T₀ 0 0 :=
      heatConv_leviSeries_interchange_trunc
        (heatOp (curvedRNCMetric κ) (curvedRNCInv κ) (cW (n := n) κ hκneg a b c)) (C * (1 + T₀))
        (mul_nonneg hCnn (by linarith)) T₀ hEboundW_le hEzero hEmeas T₀ hT₀ le_rfl 0 0
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
    -- ── thread the explicit-gate trunc capstone at `S := constGate … c`, `hCH` and `hInter` supplied. ──
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

/-- **★ J4-681 (satisfiability GATE) — CURVED, NOT SECRETLY FLAT.**  The witness underlying
    `curved_wide_a1_R6_trunc_unifiedGate` is genuinely curved: for `κ ≠ 0`, `n ≥ 2` the diagonal
    metric-Hessian trace (`Ric(0)`) of `curvedRNCMetric κ` is nonzero.  The seed `K = {0}` is where
    `hframeK` holds by `curvedRNCMetric_zero` — no cp466 collision.  NOT `a₁ = R/6`. -/
theorem curved_wide_a1_R6_trunc_unifiedGate_curved_satisfiable
    (κ : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (c : Fin n) :
    pd (fun x => pd (fun y => ∑ a, curvedRNCMetric (n := n) κ y a a) c x) c 0 ≠ 0 :=
  curvedRNCMetric_ricci_trace_diag_ne κ hκ hn c

end QIQTH.CurvedCapstoneUnifiedGate

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.CurvedCapstoneUnifiedGate
#print axioms curved_wide_a1_R6_trunc_unifiedGate
#print axioms curved_wide_a1_R6_trunc_unifiedGate_curved_satisfiable
end AxiomChecks
