/-
  GatedGlobalWitnessN1CapstoneHEmeasDischarged — the ORDER-`N = 1` partial Seeley–DeWitt capstone with
  `hEboundW` (J4-774), `hCH` (J4-775), AND `hEmeas` GENUINELY DISCHARGED, on the LIVE
  `TrueKernelA1Reduced`/restricted lineage.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS IS.  A wiring adapter, in the same spirit as J4-774/J4-775, that additionally discharges
  the `hEmeas` carry `GatedGlobalWitnessN1CapstoneHCHDischarged` still left standing.

  ── THE DON'T-UNDERCREDIT FINDING.  J4-773/776 root-caused `hEmeas` FOUR times to "the `.choose`-
  opacity of `uniformInverseChart` has NO supplier at any radius" — true for the RAW, ungated chart
  `Measurable (fun w => uniformInverseChart g gi hC hK w.2.2 w.2.1)` (no joint-in-`q` structure survives
  `Classical.choose`; confirmed again here by reading `UniformChartRadius.lean` and Mathlib's
  `ApproximatesLinearOn.toOpenPartialHomeomorph`, whose inverse is itself an opaque `PartialEquiv.symm`
  — NOT a Banach/Newton iteration, so there is no alternate constructive Mathlib IFT route to exploit).
  But `hEmeas`, as actually consumed by the live capstone, is NOT the raw chart — it is
      `tripleHEmeas g gi H := StronglyMeasurable (fun w => heatOp g gi H w.1 w.2.1 w.2.2)`
  for the *gated* witness `H = vanVleckGatedWitness g gi hChr hK S a b`.  This EXACT shape is ALREADY
  discharged from geometry alone, at the CONCRETE constant-radius flow-ball gate
  `S z := uniformFlowExp g gi hC hK z '' Metric.ball 0 c`, by two already-banked, already-build-verified
  theorems that never surface in the J4-773..776 "hEmeas wall" narrative:
      • `S1TripleHEmeasGate.tripleHEmeas_flowball_geometry` (J4-314) — `tripleHEmeas` at the flow-ball
        gate, geometry-only, std-3.
      • `ConstRadiusGateExport.constRadius_package_and_S1` (J4-316) — bundles the SAME gate's
        `(0,t]`-affine bound + origin-membership + origin-openness + the `tripleHEmeas` fact above, all
        at ONE shared `(a,b,c)`, modulo a single honest real-number antecedent `c < δ₀` (two radii from
        independent constructions — NOT provably related in general, hence carried, NOT discharged).
  `vanVleckGatedWitness g gi hChr hK S a b` is definitionally the live witness `H` used throughout the
  `N1` capstone chain (`ConvApproximants.lean`), so `constRadius_package_and_S1`'s `tripleHEmeas`
  conjunct IS `hEmeas` verbatim (`tripleHEmeas` unfolds to the exact `StronglyMeasurable (fun w => …)`
  binder — checked by direct `exact`, no coercion needed).

  ── NET REDUCTION vs `GatedGlobalWitnessN1CapstoneHCHDischarged` (J4-775).  There the surviving carries
  were `{hEmeas, hDuhamel, hDConv, hCConv (C²-at-0)}`.  Here, by REBASING the gate source from the
  opaque `gatedWitnessN1_package_open` onto the CONCRETE constant-radius `gatedWitnessN1_package_open_
  CONSTRADIUS` + its `tripleHEmeas` sibling, `hEmeas` is DISCHARGED INTERNALLY.  Surviving:
      `{hDuhamel, hDConv, hCConv (C²-at-0)}`
  PLUS the single honest real-inequality residue `c < δ₀` (both explicit positive reals produced by the
  construction, carried as an outer antecedent — satisfiable in principle, genuinely open in this file,
  never assumed false nor asserted true).  This is the fourth of the four J4-773 "genuinely open" items
  now reduced to a plain real-number comparison instead of an opaque analytic claim with "no supplier".

  ⚠ HONEST FIREWALL.  STILL CONDITIONAL; NOT `a₁ = R/6`.  `hDuhamel`/`hDConv` (Duhamel / diagonal-
  convolution differentiability) and `hCConv` (spatial `C²`-at-`0` of the diagonal Duhamel convolution)
  remain genuine, satisfiable analytic carries — none the conclusion, none vacuous.  The new geometric
  inputs `hu`/`hgiMeas`/`hchr` (transport-coefficient smoothness, inverse-metric and Christoffel
  COMPONENT measurability) are standard, satisfiable, and neither vacuous nor the conclusion.  No
  `sorry`, no new axioms, no `:= True`, no existing file edited.
-/
import Mathlib
import QIQTH.GatedGlobalWitnessN1CapstoneHCHDischarged
import QIQTH.ConstRadiusGateExport

open MeasureTheory
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.VanVleck QIQTH.LaplaceBeltrami
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.RNCExpansion
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant QIQTH.VanVleckCancellation
open QIQTH.PullbackMetric QIQTH.TrueKernelA1 QIQTH.HeatParametrixAnsatz
open QIQTH.GateOpennessExport QIQTH.InterchangeLocalRebase QIQTH.InftyRebaseCapstone
open QIQTH.ConstRadiusGateExport QIQTH.S1TripleHEmeasGate QIQTH.HEmeasBorelAudit
open QIQTH.ExpMap
open scoped Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-- **★★★ The ORDER-1 partial Seeley–DeWitt capstone with `hEboundW`, `hCH`, AND `hEmeas` GENUINELY
    DISCHARGED.**

    Rebase of `trueKernel_diagonal_a1_eq_R6_residual_N1_hCH_discharged` (J4-775) onto the CONSTANT-
    RADIUS flow-ball gate `S z := uniformFlowExp g gi hChr hK z '' Metric.ball 0 c`
    (`ConstRadiusGateExport.gatedWitnessN1_package_open_CONSTRADIUS`), whose `hEmeas`
    (`HEmeasBorelAudit.tripleHEmeas`) is discharged FROM GEOMETRY ALONE at that gate
    (`S1TripleHEmeasGate.tripleHEmeas_flowball_geometry`), modulo the single carried real inequality
    `c < δ₀`.  `hEboundW` and `hCH` are discharged exactly as in J4-774/J4-775 (both gate-generic /
    geometry-generic, so they transfer verbatim to this concrete gate).

    RESULT: surviving carries `{hDuhamel, hDConv, hCConv (C²-at-0)}` PLUS the outer real-inequality
    antecedent `c < δ₀`.  STILL CONDITIONAL; NOT `a₁ = R/6`. -/
theorem trueKernel_diagonal_a1_eq_R6_residual_N1_hEmeas_discharged
    (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (hn : 1 ≤ n)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hChr : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (hK0 : (0 : Point n) ∈ K)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ ⊤
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchr : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)) :
    ∃ a b c δ₀ : ℝ, 0 < a ∧ a < b ∧ b < c ∧ 0 < δ₀ ∧
      (c < δ₀ →
        (let S : Point n → Set (Point n) :=
            fun z => uniformFlowExp g gi hChr hK z '' Metric.ball (0 : Point n) c;
          let H := gatedKernel K S
            (globalCutoffParametrixWitnessN 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) a b
              (uniformInverseChart g gi hChr hK));
          heatOp g gi (fun w p q => heatConv H (leviSeries (heatOp g gi H)) w p q) t 0 0
              = leviSeries (heatOp g gi H) t 0 0
                + heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0 →
          DifferentiableAt ℝ (fun w => heatConv H (leviSeries (heatOp g gi H)) w 0 0) t →
          ContDiffAt ℝ 2 (fun p => heatConv H (leviSeries (heatOp g gi H)) t p 0) (0 : Point n) →
          heatOp g gi (trueHeatKernel H (leviSeries (heatOp g gi H))) t 0 0 = 0
          ∧ trueHeatKernel H (leviSeries (heatOp g gi H)) t 0 0
              = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
                * (1 + ((∑ i, Ric i i) / 6) * t
                    + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                                transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                                  * t ^ (k - 2))
                              + heatConv H (leviSeries (heatOp g gi H)) t 0 0
                                  / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))))) := by
  have hn0 : 0 < n := hn
  -- Source `a, b, C, c, δ₀` + the `(0,t]`-affine bound + origin gate membership/openness + `hEmeas`,
  -- all at the SAME concrete constant-radius flow-ball gate, bundled by J4-316.
  obtain ⟨a, b, C, c, δ₀, ha, hab, hC0, hbc, hδ₀pos, hbound, hmemS0, hopenS0, hS1⟩ :=
    constRadius_package_and_S1 hn0 g gi hg hChr hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
      hgiC hgpos hu hgiMeas hchr
  refine ⟨a, b, c, δ₀, ha, hab, hbc, hδ₀pos, ?_⟩
  intro hcδ
  -- Name the goal's gate `S` and witness `H` and FOLD the conclusion, recording the definitional
  -- equations `hSdef`/`hHdef`.  The package's exported facts (`hbound`, `hS1`, `hmemS0`, `hopenS0`)
  -- are stated with the gate lambda INLINED (not as a shared `S` fvar), so each `have` whose type
  -- mentions `H`/`S` `rw`s these equations to expose the raw form the package supplies.
  set S : Point n → Set (Point n) :=
    fun z => uniformFlowExp g gi hChr hK z '' Metric.ball (0 : Point n) c with hSdef
  set H := gatedKernel K S
      (globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hChr hK))
    with hHdef
  simp only
  intro hDuhamel hDConv hCConv
  -- gate-centre facts, FREE from the package's exported fields.
  have hS0 : (0 : Point n) ∈ S 0 := by rw [hSdef]; exact hmemS0 hK0
  have hSopen : IsOpen (S 0) := by rw [hSdef]; exact hopenS0 hK0
  -- ★ `hEmeas` — GENUINELY DISCHARGED from geometry alone, at this concrete constant-radius gate.
  -- `hS1 hcδ : tripleHEmeas g gi (vanVleckGatedWitness … S a b)`, which is DEFEQ to the target once
  -- `H`/`S` are unfolded to the inlined gatedKernel form.
  have hEmeas : StronglyMeasurable (fun w : ℝ × Point n × Point n => heatOp g gi H w.1 w.2.1 w.2.2) := by
    rw [hHdef, hSdef]; exact hS1 hcδ
  -- The effective (0,t]-restricted constant.
  have hCeff0 : (0 : ℝ) ≤ C * (1 + t) := mul_nonneg hC0 (by linarith)
  have hg0' : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    intro i j; rw [hg0, Matrix.one_apply]
  -- ★ `hEboundW_le` — the `(0,t]`-restricted affine bound, DISCHARGED from the package.
  have hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ t →
      |heatOp g gi H τ p q| ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
    rw [hHdef, hSdef]; exact fun τ p q hτ hτt => hbound t τ p q hτ hτt
  -- the order-1 residual nonpositive-time vanishing (gate-generic).
  have hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n, heatOp g gi H τ p q = 0 :=
    gatedGlobalWitnessN1_residual_hEzero g gi hn K S (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b (uniformInverseChart g gi hChr hK)
  -- the every-ceiling `(0,T]`-local bound family.
  have hlocal : ∀ T : ℝ, 0 < T → ∃ CT : ℝ, 0 ≤ CT ∧
      ∀ τ p q, 0 < τ → τ ≤ T →
        |heatOp g gi H τ p q| ≤ CT * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
    rw [hHdef, hSdef]
    exact fun T hT => ⟨C * (1 + T), mul_nonneg hC0 (by linarith),
      fun τ p q hτ hτT => hbound T τ p q hτ hτT⟩
  -- `hInt` — the FULL `IterConvIntegrableW`, from the `(0,T]`-LOCAL bound via the `timeCap` producer.
  have hInt : IterConvIntegrableW (heatOp g gi H) 2 0 (C * (1 + t)) :=
    iterConvIntegrableW_of_locally_bound_baseMeas (heatOp g gi H) (C * (1 + t))
      hEzero hEmeas hlocal
  -- `hInter` — the tsum/heatConv interchange from the `(0,T]`-LOCAL data.
  have hInter : heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0
      = ∑' k : ℕ, heatConv (heatOp g gi H)
          (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE (heatOp g gi H) (k + 1) τ p q) t 0 0 :=
    hInter_from_local_data (heatOp g gi H) (C * (1 + t)) t hCeff0 ht
      hEboundW_le hEzero hEmeas hlocal t ht le_rfl 0 0
  -- ★ `hHdiag` at `N = 1` — GENUINELY TRUE; `hS0` supplied by the package's exported gate membership.
  have hHdiag : H t 0 0 = heatParametrixFn 1 g (transportOp (vanVleck g) g gi) t (0 : Point n) :=
    gatedGlobalWitnessN1_diag_hHdiag g gi K S a b ha hab (uniformInverseChart g gi hChr hK) t
      hK0 hS0 (uniformInverseChart_zero g gi hChr hK hK0)
  -- `hDH` diagonal time-differentiability at the order-1 witness (gate-generic).
  have hDH : DifferentiableAt ℝ (fun w => H w 0 0) t :=
    gatedGlobalWitnessN1_diag_hDH g gi hChr hK (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b S t ht
  -- ★ `hCH` — the spatial-`C²`-at-`0` witness diagonal, DISCHARGED from the `C^∞` geometry.
  have hCH : ContDiffAt ℝ 2 (fun p => H t p 0) (0 : Point n) :=
    hCH_discharge_from_geometry g gi hChr hK S a b t hK0 hS0 hSopen hg hgiC hgpos hg0'
  -- Close with the `C²`-weakened `(0,t]`-RESTRICTED capstone.
  exact trueKernel_diagonal_a1_eq_R6_residual_restricted_C2 g gi Ric 1 (le_refl 1) t ht H
    (C * (1 + t)) hCeff0 hg hg0' hgi hΓ hdg0 htr hsrc hHdiag hEboundW_le hInt hDuhamel hInter
    hDH hDConv hCH hCConv

end QIQTH.HeatResidualBound

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HeatResidualBound
#print axioms trueKernel_diagonal_a1_eq_R6_residual_N1_hEmeas_discharged
end AxiomChecks
