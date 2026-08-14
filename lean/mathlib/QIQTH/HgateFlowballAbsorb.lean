/-
  HgateFlowballAbsorb — J4-741: the FLOWBALL-DRIVEN closing brick — ABSORB `hgate` (and the cheap
  `hmemS0`) into a v2-descended capstone from PURE GEOMETRY, via the metric-agnostic flow-ball producer
  `CurvedHgateGlue.hgate_width43_quad_affine_flowball`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (J4-741) THE SCOPING VERDICT — why this is a v2-based ∃-capstone, NOT a v3/v4 absorption.

  The task was to wire the two already-proven-but-unconnected items
    (1) `CurvedHgateGlue.hgate_width43_quad_affine_flowball`  — PRODUCES `∃ a b c P₀ P₁, …` the on-gate
        width-4/3 quadratic-affine `hgate`, from geometry alone (no `hgate` assumption); and
    (2) `ConcreteGateInstantiation.hKSmeas_concrete`          — PRODUCES `∃ δ₀ > 0, ∀ c < δ₀, …` the
        FULL-gate `MeasurableSet`, from geometry alone,
  into the strongest capstone.  A FRESH-AUDIT verdict (types read, not names):

  • SHAPE MISMATCH with v3/v4.  `ConstRadiusAbsorb.a1_R6_from_data_v3` (and `SlotsThreading`'s v4) take
    `hgate` as `∀ a b c, 0<a→a<b→b<c → ∃ P₀ P₁, …` (∀-OVER-GATES) and `hKSmeas` as `∀ c, MeasurableSet …`
    (∀-OVER-RADII).  The two producers give a SINGLE self-chosen triple / a δ₀-BOUNDED radius family.
    The width-4/3 bound is FALSE at an arbitrary admissible `(a,b,c)` (the radii `a,b` are the cutoff
    radii chosen inside the width-1 residual; `c` is derived from them), so the flow-ball producer CANNOT
    supply v3/v4's ∀-over-gates `hgate`; and `hKSmeas_concrete` is δ₀-bounded so cannot supply v3/v4's
    `∀ c`.  Hence NEITHER producer fits the v3/v4 architecture.  They fit the SPECIFIC-TRIPLE shape of
    `HGaussAbsorb.a1_R6_from_data_v2`.

  • RADIUS OPACITY blocks co-absorbing `hgate` + `hKSmeas`.  The flow-ball producer HIDES its `c` (an
    opaque `∃`); `hKSmeas_concrete` needs `c < δ₀` (also opaque).  Two opaque existentials cannot be
    compared, so `hKSmeas` CANNOT be discharged at the flow-ball producer's gate.  `hKSmeas` therefore
    stays a carried binder here (this is the SAME radius-alignment wall the tower's `WhiteGated`
    co-instantiation machinery — J4-707 — exists to break; not a mechanical wire).

  • THE ACHIEVABLE, HONEST WIRE.  Commit the conclusion to the flow-ball producer's OWN triple (∃-over
    radii, exactly as v3's Route (ii)).  Then `hgate` is DISCHARGED INTERNALLY from geometry, and the
    base-point membership `hmemS0` is discharged at the flow-ball gate via `φ_0 0 = 0`
    (`uniformFlowExp_zero`).  The remaining `(a,b,c)`-dependent v2 carriers (`hKSmeas`, `hpkgBound`,
    `hopenS0`, `hcarTau`/`hcarField`/`hcarField2`, `slots`) are carried ∀-over-gates and evaluated at the
    produced triple.  This is a DIFFERENT reduction branch from v3: v3 absorbs the width-2 package
    (`hpkgBound`/`hmemS0`/`hopenS0`) and carries `hgate`; this file absorbs the substantive width-4/3
    analytic carrier `hgate` (+ `hmemS0`) and carries the width-2 package.  Neither dominates — the two
    producers commit to DIFFERENT gates.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  Absorbing
  `hgate` (+ `hmemS0`) removes exactly those two carriers from the v2 surface at the flow-ball gate; it
  closes NOTHING deeper.  What remains CONDITIONAL (UNCHANGED in content):
    • the CONVERGENCE-TRIO content living inside the `A1R6GateSlots` Duhamel census — NEVER claimed closed;
    • the `hcarTau`/`hcarField`/`hcarField2` jet-supplier existentials — carried ∀-over-gates;
    • the width-2 package `hpkgBound`/`hopenS0` and the measurability `hKSmeas` — carried (radius opacity);
    • the base-metric identification `hgPull` and the F4 pullback residues (group (D′)).
  No `sorry`, no `admit`, no `:= True`, no new axiom (`std-3` only), no vacuous / unsatisfiable
  hypothesis (the flow-ball producer's `hframeK` holds on `K = {0}` by `curvedRNCMetric_zero` — the cp466
  witness gate, no J4-548 collision), no existing file edited.  `a₁ = R/6` stays CONDITIONAL.
-/
import Mathlib
import QIQTH.HGaussAbsorb
import QIQTH.CurvedHgateGlue

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

namespace QIQTH.HgateFlowballAbsorb

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (J4-741) `a1_R6_from_data_v4b` — v2 with `hgate` + `hmemS0` ABSORBED from geometry.
    ############################################################################### -/

/-- **★★★★★ J4-741 — `a1_R6_from_data_v4b`.**  The capstone `HGaussAbsorb.a1_R6_from_data_v2` RESTATED
    WITHOUT its `hgate` binder and WITHOUT its `hmemS0` binder — both discharged INTERNALLY from
    geometry-only inputs:
      • `hgate` ← `CurvedHgateGlue.hgate_width43_quad_affine_flowball` (the metric-agnostic flow-ball
        producer), which — from `hg`/`hChr`/`hK`/`hgnd`/`hgsymm`/`hinvF`/`hframeK`/`hw`/`hdg0`/`hg0` —
        PRODUCES gate radii `0 < a < b < c` and affine constants `P₀, P₁ ≥ 0` with the on-gate width-4/3
        quadratic-affine bound at the LITERAL flow-ball gate `constGate g gi hChr hK c` (defeq to
        `fun z => uniformFlowExp g gi hChr hK z '' Metric.ball 0 c`);
      • `hmemS0` ← `φ_0 0 = 0` (`uniformFlowExp_zero`) with `0 ∈ K` and `0 < c`.
    Because the gate radii are now internal geometric data, the CONCLUSION is existentially quantified
    over `(a,b,c)` (Route (ii), exactly as v3); the remaining `(a,b,c)`-dependent v2 carriers are supplied
    ∀-QUANTIFIED over admissible gate triples and evaluated at the produced triple.

    ⚠ THE HONEST SUMMARY.  Maximally-unconditional **CONDITIONAL** a₁ two-jet, NOT `a₁ = R/6`.  Absorbing
    `hgate` + `hmemS0` removes exactly those two carriers at the flow-ball gate; it closes nothing deeper.
    What remains CONDITIONAL: the `A1R6GateSlots` censuses (Duhamel/W1-free/L2 — the convergence-trio
    content), `hcarTau`/`hcarField`/`hcarField2`, the width-2 package `hpkgBound`/`hopenS0`, the
    measurability `hKSmeas`, the base-metric identification `hgPull` (group (D′)).  ⚠ NOT `a₁ = R/6`. -/
theorem a1_R6_from_data_v4b (hn : 1 ≤ n)
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
    -- ── (A′) the flow-ball producer's EXTRA geometry-only inputs (satisfiable; `hframeK` holds on `K={0}`):
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
    -- the width-2 package `hpkgBound`, ∀-over-gates with its constant (radius opacity ⟹ NOT absorbed):
    (hpkgBoundG : ∀ a b c : ℝ, 0 < a → a < b → b < c →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ t' : ℝ, ∀ τ p q, 0 < τ → τ ≤ t' →
          |heatOp g gi (vanVleckGatedWitness g gi hChr hK (constGate g gi hChr hK c) a b) τ p q|
            ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
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
  -- ── extract the ∀-over-gates carriers AT the produced (admissible) gate triple.
  obtain ⟨C, hCnn, hpkgBound⟩ := hpkgBoundG a b c ha hab hbc
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

end QIQTH.HgateFlowballAbsorb

/-! ###############################################################################
    ### THE AUDIT — `#print axioms` for the capstone (must be `std-3`).
    ############################################################################### -/
section AxiomChecks
open QIQTH.HgateFlowballAbsorb
#print axioms a1_R6_from_data_v4b
end AxiomChecks
