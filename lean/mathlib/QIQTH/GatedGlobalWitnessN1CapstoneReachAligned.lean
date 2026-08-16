/-
  GatedGlobalWitnessN1CapstoneReachAligned — the ORDER-`N = 1` partial Seeley–DeWitt capstone with
  `hEboundW`, `hCH`, `hEmeas` GENUINELY DISCHARGED **AND the `c < δ₀` reach side condition CLOSED**,
  on the LIVE `TrueKernelA1Reduced`/restricted lineage.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  WHAT THIS IS.  A strict strengthening of J4-777
  (`GatedGlobalWitnessN1CapstoneHEmeasDischarged.trueKernel_diagonal_a1_eq_R6_residual_N1_hEmeas_discharged`),
  which left standing the single OUTER real-number antecedent `c < δ₀` — "two independently-constructed
  radii, not provably related in general".  Here that antecedent is DISCHARGED at the root, so the
  capstone's `hEmeas` conjunct holds UNCONDITIONALLY (no `c < δ₀ →` wrapper).

  ── HOW THE `c < δ₀` WALL IS BROKEN (no new mathematics).  J4-777 carried `c < δ₀` because the S1
  jet reach `δ₀` was produced by `ConstRadiusGateExport.constRadius_package_and_S1` only AFTER the
  cutoff parameters `(a,b)` and the package's own gate radius `c = (b+ρc)/2` — two disjoint ∃-chains
  with no proven comparison.  But the J4-599 reach-alignment infrastructure already dissolves exactly
  this obstruction on the CURVED lineage; the SAME two hoisted-replay bricks apply verbatim to the
  flat/van-Vleck live lineage here:
      • `ReachRequant.tripleHEmeas_flowball_requant` — the audited ∃∀-swap: every S1-supplier radius
        bottoms out in `(a,b)`-FREE geometry lemmas, so the jet reach `δ₀ > 0` is available BEFORE the
        gate parameters `(a,b,c)`.
      • `CurvedA1ReachAlign.gatedWitnessN1_hEboundW_le_lin_CONST_prescribed` — the banked constant-radius
        width-2 defect-bound producer replayed with a PRESCRIBED extra radius ceiling `ε`, so the
        exposed gate radius `c = (b+ρc)/2` additionally satisfies `c < ε` (shrinking `ρc` preserves the
        original proof line-for-line; this producer is GENERIC in `(Θ,u)`, so it serves the
        `Θ = vanVleck g`, `u = transportCoeff …` live lineage directly).
  Choosing `ε := δ₀(jet)` aligns the two chains: the package's own `c` satisfies `c < δ₀`, so the
  requant S1 fires with NO antecedent.  This is the exact analogue, on the LIVE lineage, of J4-599's
  `curved_hBdom_unconditional` reach-alignment; nothing here is `a₁ = R/6`, no radius comparison is
  assumed, no inequality reversed — the produced gate `0 < a < b < c` remains genuinely inhabited with
  `c < min(chart-reach, jet-reach)`, a small but nonempty gate the capstone consumes as free parameters.

  ── NET REDUCTION vs `…_N1_hEmeas_discharged` (J4-777).  There the surviving carries were
  `{hDuhamel, hDConv, hCConv (C²-at-0)}` PLUS the outer `c < δ₀`.  Here the outer `c < δ₀` is GONE.
  Surviving: `{hDuhamel, hDConv, hCConv (C²-at-0)}` only — the three genuine, satisfiable analytic
  differentiability carries.

  ⚠ HONEST FIREWALL.  STILL CONDITIONAL; NOT `a₁ = R/6`.  `hDuhamel`/`hDConv` (Duhamel / diagonal-
  convolution differentiability) and `hCConv` (spatial `C²`-at-`0` of the diagonal Duhamel convolution)
  remain genuine, satisfiable analytic carries — none the conclusion, none vacuous.  The geometric
  inputs `hu`/`hgiMeas`/`hchr`/`hgiC`/`hgpos` (transport-coefficient smoothness, inverse-metric and
  Christoffel component measurability, inverse-metric smoothness, positive metric determinant) are
  standard, satisfiable, and neither vacuous nor the conclusion.  No `sorry`, no new axioms, no
  `:= True`, no existing file edited.
-/
import Mathlib
import QIQTH.GatedGlobalWitnessN1CapstoneHEmeasDischarged
import QIQTH.ConstRadiusGateExport
import QIQTH.ReachRequant
import QIQTH.CurvedA1ReachAlign

open MeasureTheory
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.VanVleck QIQTH.LaplaceBeltrami
open QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.RNCExpansion
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel
open QIQTH.HeatResidualBound QIQTH.GaussianWidthTolerant QIQTH.VanVleckCancellation
open QIQTH.PullbackMetric QIQTH.TrueKernelA1 QIQTH.HeatParametrixAnsatz
open QIQTH.GateOpennessExport QIQTH.InterchangeLocalRebase QIQTH.InftyRebaseCapstone
open QIQTH.ConstRadiusGateExport QIQTH.S1TripleHEmeasGate QIQTH.HEmeasBorelAudit
open QIQTH.ReachRequant QIQTH.CurvedA1ReachAlign
open QIQTH.ExpMap
open scoped Topology

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-- **★★ The reach-aligned constant-radius package + S1, with `c < δ₀` DISCHARGED.**  The unconditional
    analogue of `ConstRadiusGateExport.constRadius_package_and_S1`: the same constant-radius flow-ball
    gate package (`(0,t]`-affine bound + origin gate membership + origin gate-openness) at one shared
    `(a,b,c)`, bundled with the S1 fact `HEmeasBorelAudit.tripleHEmeas` at that SAME gate — but NOW with
    the jet-reach smallness `c < δ₀` secured INTERNALLY (no carried antecedent).

    Mechanism: `ReachRequant.tripleHEmeas_flowball_requant` produces the jet reach `δ₀ > 0` BEFORE the
    gate parameters; feeding `ε := δ₀` to `CurvedA1ReachAlign.gatedWitnessN1_hEboundW_le_lin_CONST_prescribed`
    yields a package whose gate radius `c` satisfies `c < δ₀`, so the requant S1 fires unconditionally.
    NOT `a₁ = R/6`. -/
theorem constRadius_package_and_S1_reachAligned (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) k))
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e (0 : Point n) = 0)
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0)
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchr : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)) :
    ∃ a b C c : ℝ,
      0 < a ∧ a < b ∧ 0 ≤ C ∧ b < c ∧
      (∀ (t : ℝ), ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (gatedKernel K
            (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c)
            (globalCutoffParametrixWitnessN 1 (vanVleck g)
              (transportCoeff (transportOp (vanVleck g) g gi)) a b
              (uniformInverseChart g gi hC hK))) τ p q|
          ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
      ∧ ((0 : Point n) ∈ K →
          (0 : Point n) ∈ uniformFlowExp g gi hC hK 0 '' Metric.ball (0 : Point n) c)
      ∧ ((0 : Point n) ∈ K →
          IsOpen (uniformFlowExp g gi hC hK 0 '' Metric.ball (0 : Point n) c))
      ∧ QIQTH.HEmeasBorelAudit.tripleHEmeas g gi
          (vanVleckGatedWitness g gi hC hK
            (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) a b) := by
  -- (i) the jet reach `δ₀ > 0`, produced BEFORE the gate parameters `(a,b,c)`.
  obtain ⟨δ₀, hδ0, hS1spec⟩ :=
    tripleHEmeas_flowball_requant hn g gi hC hK hg hgiC hgpos hu hgiMeas hchr
  -- (ii) the two van-Vleck coefficient bounds feeding the constant-radius producer.
  obtain ⟨ρ0, hρ0, C0, hC0, hb0⟩ :=
    hCoeffU0_vanVleck g gi hg hC hK hgnd hgsymm hinvF hframeK
      (transportOp (vanVleck g) g gi) (hw 0) hdg0 hg0
  obtain ⟨ρ1, hρ1, C1, hC1, hb1⟩ :=
    uniformCoeffLinear_bound g gi hg hC hK hgnd hgsymm hinvF hframeK (vanVleck g)
      (fun j => transportCoeff (transportOp (vanVleck g) g gi) (j + 1)) (hw 1)
  set ρ_c : ℝ := min ρ0 ρ1 with hρc_def
  have hρc0 : 0 < ρ_c := lt_min hρ0 hρ1
  -- (iii) the PRESCRIBED-ceiling package with `ε := δ₀`, forcing the gate radius `c < δ₀`.
  obtain ⟨a, b, C, c, ha, hab, hC0', hbc, hcδ, hbound, _hgate, hmemS, hopenS⟩ :=
    gatedWitnessN1_hEboundW_le_lin_CONST_prescribed g gi hg hC hK hgnd hgsymm hinvF hframeK
      (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) hw
      ρ_c C0 C1 hρc0 hC0 hC1
      (fun q hq v hv => hb0 q hq v (lt_of_lt_of_le hv (min_le_left _ _)))
      (fun q hq v hv => hb1 q hq v (lt_of_lt_of_le hv (min_le_right _ _)))
      δ₀ hδ0
  refine ⟨a, b, C, c, ha, hab, hC0', hbc, hbound, ?_, ?_, ?_⟩
  · intro h0; exact hmemS 0 h0
  · intro h0; exact hopenS 0 h0
  -- (iv) S1 fires UNCONDITIONALLY: `c < δ₀` is now proved (`hcδ`), not carried.
  · exact hS1spec a b ha hab c hbc hcδ

/-- **★★★ The ORDER-1 partial Seeley–DeWitt capstone with `hEboundW`, `hCH`, `hEmeas` DISCHARGED AND
    the `c < δ₀` reach side condition CLOSED.**

    Strict strengthening of J4-777's
    `trueKernel_diagonal_a1_eq_R6_residual_N1_hEmeas_discharged`: the existential is now
    `∃ a b c, 0 < a ∧ a < b ∧ b < c ∧ (…)` with NO `δ₀` binder and NO `c < δ₀ →` antecedent — the S1
    measurability slot is discharged internally by `constRadius_package_and_S1_reachAligned`.  `hEboundW`
    and `hCH` are discharged exactly as in J4-774/J4-775/J4-777.

    RESULT: surviving carries `{hDuhamel, hDConv, hCConv (C²-at-0)}` ONLY.  STILL CONDITIONAL; NOT
    `a₁ = R/6`. -/
theorem trueKernel_diagonal_a1_eq_R6_residual_N1_reachAligned
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
    ∃ a b c : ℝ, 0 < a ∧ a < b ∧ b < c ∧
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
                                / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2)))) := by
  have hn0 : 0 < n := hn
  -- Source `a, b, C, c` + the `(0,t]`-affine bound + origin gate membership/openness + `hEmeas`
  -- (S1), all at the SAME concrete constant-radius flow-ball gate, with `c < δ₀` DISCHARGED.
  obtain ⟨a, b, C, c, ha, hab, hC0, hbc, hbound, hmemS0, hopenS0, hS1⟩ :=
    constRadius_package_and_S1_reachAligned hn0 g gi hg hChr hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
      hgiC hgpos hu hgiMeas hchr
  refine ⟨a, b, c, ha, hab, hbc, ?_⟩
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
  -- ★ `hEmeas` — GENUINELY DISCHARGED, UNCONDITIONALLY (no `c < δ₀` antecedent).
  have hEmeas : StronglyMeasurable (fun w : ℝ × Point n × Point n => heatOp g gi H w.1 w.2.1 w.2.2) := by
    rw [hHdef, hSdef]; exact hS1
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
#print axioms constRadius_package_and_S1_reachAligned
#print axioms trueKernel_diagonal_a1_eq_R6_residual_N1_reachAligned
end AxiomChecks
