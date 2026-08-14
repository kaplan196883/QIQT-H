/-
  HgatePkgFlowballAbsorb — J4-744: THE FLOWBALL DOUBLE-ABSORPTION — `hgate` **AND** `hpkgBound`
  (the width-2 package bound) absorbed into a v2-descended capstone from PURE GEOMETRY, at ONE
  shared flow-ball gate.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (J4-744) THE DOUBLE-WIN — why the radius-opacity blocker of J4-741/743 does NOT recur here.

  `HgateFlowballAbsorb.a1_R6_from_data_v4b` (J4-741) absorbed `hgate` (+ `hmemS0`) at the flow-ball
  gate but had to CARRY the width-2 package `hpkgBoundG` ∀-over-gates, because the width-2 package's
  banked supplier (`ConstRadiusGateExport.constRadius_package_and_S1`) produces its OWN opaque-∃ gate
  radius, incomparable with the flow-ball producer's opaque-∃ radius (the J4-741/743 RADIUS-OPACITY
  wall — two independent existentials at DIFFERENT gates cannot be aligned).

  ⭐ THE DISSOLUTION (J4-680 gate-unification, applied here).  The width-2 `hpkgBound` need NOT come
  from the independent `constRadius_package_and_S1` supplier at all.  It is a **width-widening
  consequence of the SAME `hgate`** at the SAME flow-ball gate, via the banked chain

    `hgate` (width-4/3 quad-affine, flow-ball gate)
        ──[`HgateAffineRepair.hEdom_vanVleck_of_hgate_affine`]──▶  `hEdom` (width-3/2 Gaussian)
        ──[`gaussDdim_le_gaussDdim_chart` at (3/2,2) + affine→(1+t') rescale]──▶  width-2 `hpkgBound`.

  Both steps are METRIC-AGNOSTIC and reference the flow-ball gate `constGate g gi hChr hK c`
  (defeq `fun z => uniformFlowExp g gi hChr hK z '' Metric.ball 0 c`) — exactly the gate the flow-ball
  producer commits to.  So there is NO second opaque existential to align: `hpkgBound` is DERIVED from
  `hgate`, at `hgate`'s own gate.  This is the same width-widening `CurvedUnifiedGateBounds.
  curvedRNC_unified_gate_bounds` performs for the curved witness, hoisted to the metric-agnostic
  producer and threaded into the v2 capstone.

  Net: `a1_R6_from_data_v4c` absorbs BOTH `hgate` (v4b's win) AND `hpkgBound` (which v4b carried as
  `hpkgBoundG`) AND `hmemS0`, from geometry alone, at ONE gate — a strict improvement over BOTH
  `v3` (which carries `hgate`) and `v4b` (which carries `hpkgBoundG`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  Absorbing
  `hgate` + `hpkgBound` + `hmemS0` removes exactly those carriers from the v2 surface at the flow-ball
  gate; it closes NOTHING deeper.  What remains CONDITIONAL (UNCHANGED in content):
    • the CONVERGENCE-TRIO content living inside the `A1R6GateSlots` Duhamel census — NEVER claimed
      closed (the `slots` carrier still bundles `hDuhamel`/`hDConv`/`hCConv`, whose deepest inputs
      — Levi/true-kernel convergence `hBoundaryLim`, Seeley-DeWitt delta-mass `hmassone` — are carried
      as hypotheses by EVERY core-threading theorem; no geometry-only supplier exists);
    • the `hcarTau`/`hcarField`/`hcarField2` jet-supplier existentials — carried ∀-over-gates;
    • the origin gate-openness `hopenS0` and the measurability `hKSmeas` — carried (radius opacity);
    • the base-metric identification `hgPull` and the F4 pullback residues (group (D′)).
  No `sorry`, no `admit`, no `:= True`, no new axiom (`std-3` only), no vacuous / unsatisfiable
  hypothesis (the flow-ball producer's `hframeK` holds on `K = {0}` by `curvedRNCMetric_zero` — the
  cp466 witness gate, no J4-548 collision), no existing file edited.  `a₁ = R/6` stays CONDITIONAL.
-/
import Mathlib
import QIQTH.HGaussAbsorb
import QIQTH.CurvedUnifiedGateBounds

open MeasureTheory Finset Filter Set
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.RadialTransport
open QIQTH.ParametrixFunction QIQTH.VanVleck QIQTH.HeatTransportRecursion
open QIQTH.VanVleckCancellation QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.HeatParametrixAnsatz QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.ErrorKernelFactorization
open QIQTH.DataPileWitnessAudit QIQTH.HEmeasBorelAudit QIQTH.PullbackMetric
open QIQTH.HeatKernelA1 QIQTH.ExpMap
open QIQTH.A1R6CoreAtGate QIQTH.A1R6SlotAdapters QIQTH.ConstGateAssembly QIQTH.FinalA1Slots
open QIQTH.HgateAffineRepair QIQTH.GatedRepSFix
open QIQTH.A1R6FromData QIQTH.HGaussAbsorb QIQTH.CurvedHgateGlue
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.HgatePkgFlowballAbsorb

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (J4-744) `a1_R6_from_data_v4c` — v2 with `hgate` + `hpkgBound` + `hmemS0` ABSORBED.
    ############################################################################### -/

/-- **★★★★★ J4-744 — `a1_R6_from_data_v4c`.**  The capstone `HGaussAbsorb.a1_R6_from_data_v2`
    RESTATED WITHOUT its `hgate` binder, WITHOUT its width-2 package binder `hpkgBound`, and WITHOUT
    its `hmemS0` binder — all THREE discharged INTERNALLY from geometry-only inputs at ONE shared
    flow-ball gate:
      • `hgate` ← `CurvedHgateGlue.hgate_width43_quad_affine_flowball` (metric-agnostic flow-ball
        producer): produces gate radii `0 < a < b < c` and affine constants `P₀, P₁ ≥ 0` with the
        on-gate width-4/3 quadratic-affine bound at `constGate g gi hChr hK c`;
      • `hpkgBound` ← that SAME `hgate`, width-widened: `hEdom_vanVleck_of_hgate_affine` bridges
        width-4/3 → width-3/2 Gaussian `hEdom`, then `gaussDdim_le_gaussDdim_chart` at `(3/2,2)` plus
        an affine→`(1+t')` rescale widens `hEdom` to the width-2 all-`t'` package bound
        `(C·(1+t'))·baseKernelW 2 0 τ p q` at the SAME gate (NO independent radius supplier — the
        radius-opacity wall of J4-741/743 is DISSOLVED);
      • `hmemS0` ← `φ_0 0 = 0` (`uniformFlowExp_zero`) with `0 ∈ K` and `0 < c`.

    ⚠ THE HONEST SUMMARY.  Maximally-unconditional **CONDITIONAL** a₁ two-jet, NOT `a₁ = R/6`.
    Absorbing `hgate` + `hpkgBound` + `hmemS0` removes exactly those carriers at the flow-ball gate;
    it closes nothing deeper.  What remains CONDITIONAL: the `A1R6GateSlots` censuses (Duhamel/W1-free/
    L2 — the convergence-trio content), `hcarTau`/`hcarField`/`hcarField2`, the origin gate-openness
    `hopenS0`, the measurability `hKSmeas`, the base-metric identification `hgPull` (group (D′)).
    ⚠ NOT `a₁ = R/6`. -/
theorem a1_R6_from_data_v4c (hn : 1 ≤ n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    -- ── (A) base geometry / gauge binders (unchanged from v2):
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
    -- ── (A′) the flow-ball producer's EXTRA geometry-only inputs (satisfiable; `hframeK` on `K={0}`):
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchrMeas : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p))
    -- ── (B) the remaining `(a,b,c)`-dependent v2 carriers, ∀-QUANTIFIED over admissible gate triples:
    -- the v2 measurability carriers, ∀-over-gates (radius opacity ⟹ NOT absorbed):
    (hKSmeas : ∀ c : ℝ, MeasurableSet {w : ℝ × Point n × Point n |
        w.2.2 ∈ K ∧ w.2.1 ∈ constGate g gi hChr hK c w.2.2})
    (hcarTau : ∀ a b c : ℝ, 0 < a → a < b → b < c →
        ∃ Cfield : Point n → Point n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable (fun w : ℝ × Point n × Point n => Cfield w.2.2 w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ constGate g gi hChr hK c w.2.2 →
            HasDerivAt (fun u : ℝ => chartFieldAmp g gi hChr hK a b u w.2.2 w.2.1)
              (Cfield w.2.2 w.2.1) w.1))
    (hcarField : ∀ a b c : ℝ, 0 < a → a < b → b < c → ∀ k : Fin n,
        ∃ Pfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ (∀ j, Measurable (fun w : ℝ × Point n × Point n => Pfield w.2.2 w.2.1 j))
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => chartFieldAmp g gi hChr hK a b w.1 w.2.2 w.2.1)
        ∧ Measurable
            (fun w : ℝ × Point n × Point n => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ constGate g gi hChr hK c w.2.2 →
            IsOpen (constGate g gi hChr hK c w.2.2) ∧
            (∀ j, HasDerivAt
              (fun s : ℝ => uniformInverseChart g gi hChr hK w.2.2 (Function.update w.2.1 k s) j)
              (Pfield w.2.2 w.2.1 j) (w.2.1 k)) ∧
            PdiffAt (chartFieldAmp g gi hChr hK a b w.1 w.2.2) k w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∉ constGate g gi hChr hK c w.2.2 →
            witnessFieldDeriv g gi hChr hK (constGate g gi hChr hK c) a b k w.1 w.2.1 w.2.2 = 0))
    (hcarField2 : ∀ a b c : ℝ, 0 < a → a < b → b < c → ∀ i j : Fin n,
        ∃ Pifield Pjfield Qfield : Point n → Point n → Fin n → ℝ,
        Measurable (fun w : ℝ × Point n × Point n => uniformInverseChart g gi hChr hK w.2.2 w.2.1)
        ∧ (∀ k, Measurable (fun w : ℝ × Point n × Point n => Pifield w.2.2 w.2.1 k))
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
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∈ constGate g gi hChr hK c w.2.2 →
            IsOpen (constGate g gi hChr hK c w.2.2) ∧
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
            PdiffAt (fun y => pd (chartFieldAmp g gi hChr hK a b w.1 w.2.2) j y) i w.2.1)
        ∧ (∀ w : ℝ × Point n × Point n, w.2.2 ∈ K → 0 < w.1 →
            w.2.1 ∉ constGate g gi hChr hK c w.2.2 →
            pd (fun y => pd (fun x =>
                vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b w.1 x w.2.2) j y)
              i w.2.1 = 0))
    -- the origin gate-openness `hopenS0`, ∀-over-radii (radius opacity ⟹ NOT absorbed):
    (hopenS0 : ∀ c : ℝ, (0 : Point n) ∈ K → IsOpen (constGate g gi hChr hK c 0))
    -- the ONE semantic slot package (Duhamel + W1-free + L2 censuses bundled), ∀-over-gates:
    (slots : ∀ a b c : ℝ, 0 < a → a < b → b < c → A1R6GateSlots g gi hChr hK c a b t)
    -- ── (D′) group (D) ABSORBED (unchanged from v2): base-metric exp-pullback + base geometry premises.
    (gb gib : Point n → Fin n → Fin n → ℝ)
    (hCb : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel gb gib a b c y))
    (hgPull : g = expPullbackMetric gb gib hCb 0)
    (hsymmb : ∀ y a b, gb y a b = gb y b a)
    (hinvb : ∀ y a b, (∑ σ, gb y a σ * gib y σ b) = if a = b then 1 else 0)
    (hgb : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gb y a b))
    (hgaugeb : ∀ a b, gb 0 a b = if a = b then 1 else 0) :
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
  -- ── consume the flow-ball producer: obtain the gate radii + the on-gate width-4/3 quad-affine `hgate`.
  obtain ⟨a, b, c, P₀, P₁, ha, hab, hbc, hP₀, hP₁, hgate⟩ :=
    hgate_width43_quad_affine_flowball g gi hg hChr hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
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
    -- width-widening `gaussDdim (3/2·τ) (p-q) ≤ Sc · gaussDdim (2·τ) (p-q)`.
    have hwiden : gaussDdim (3 / 2 * τ) (p - q) ≤ Sc * gaussDdim (2 * τ) (p - q) := by
      have hchart := gaussDdim_le_gaussDdim_chart (n := n) (c := 3 / 2) (d := 2)
        (by norm_num) (by norm_num) hτ (v := p - q) (w := p - q)
        (by nlinarith [rncRadialSq_nonneg (p - q)])
      rw [hScdef]; exact hchart
    have hbk : baseKernelW (2 : ℝ) (0 : ℝ) τ p q = gaussDdim (2 * τ) (p - q) :=
      baseKernelW_zero_apply (2 : ℝ) τ p q
    -- affine outer factor: `(E₀+E₁τ) ≤ (E₀+E₁)(1+t')`.
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
  -- ── `hmemS0` discharged at the flow-ball gate: `φ_0 0 = 0` (`uniformFlowExp_zero`), `0 ∈ K`, `0 < c`.
  have hmemS0 : (0 : Point n) ∈ K → (0 : Point n) ∈ constGate g gi hChr hK c 0 := by
    intro _
    refine ⟨0, ?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_zero]; exact hc0
    · exact uniformFlowExp_zero g gi hChr hK 0 hK0
  -- ── assemble the ∃-quantified conclusion and re-export the CONDITIONAL two-jet from `v2`.
  refine ⟨a, b, c, ha, hab, hbc, ?_⟩
  exact a1_R6_from_data_v2 hn g gi t ht hChr hK hK0
    hg hgsymm hgiC hgpos hg0 hgi hΓ hdg0 hsrc a b c C ha hab hbc hCnn
    P₀ P₁ hP₀ hP₁ hgate
    (hKSmeas c) (hcarTau a b c ha hab hbc) (hcarField a b c ha hab hbc) (hcarField2 a b c ha hab hbc)
    hgiMeas hchrMeas
    hpkgBound hmemS0 (hopenS0 c)
    (slots a b c ha hab hbc)
    gb gib hCb hgPull hsymmb hinvb hgb hgaugeb

end QIQTH.HgatePkgFlowballAbsorb

/-! ###############################################################################
    ### THE AUDIT — `#print axioms` for the capstone (must be `std-3`).
    ############################################################################### -/
section AxiomChecks
open QIQTH.HgatePkgFlowballAbsorb
#print axioms a1_R6_from_data_v4c
end AxiomChecks
