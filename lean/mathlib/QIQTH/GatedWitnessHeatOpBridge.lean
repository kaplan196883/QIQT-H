/-
  GatedWitnessHeatOpBridge — J4-286: the gated-witness `heatOp` bridge.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  THE TARGET.  `ParametrixSpatialPartials.heatOpWitness_jointContinuousOn_geometry` (J4-285) gives the
  joint `(τ,z)`-continuity of `heatOp` applied to the PLAIN `heatParametrix` kernel
  `fun s p _ => heatParametrix N Θ u s p` on `Icc t₁ t₂ ×ˢ closedBall 0 R` (`0 < t₁`), carrying only
  coefficient regularity + the geometry continuities of `gi`/`christoffel`.  The Levi/boundary chain,
  however, consumes the concrete kernel

      `E τ z := heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) τ z 0`,

  the GATED, radially-CUT-OFF, CHART-TRANSPORTED order-1 van-Vleck witness (base point `q = 0` fixed).
  This file peels the witness down to a `heatParametrix` core and records EXACTLY how much of the way
  to J4-285 that reduction reaches.

  ─────────────────────────────────────────────────────────────────────────────────────────────
  THE DEFINITIONAL CHAIN (verbatim from `ConvApproximants` / `AmplitudePackage`).
      `vanVleckGatedWitness g gi hC hK S a b`
        `= gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ* u* a b W)`                    (def)
  and ON THE GATE (`q ∈ K`, `p ∈ S q`),
      `globalCutoffParametrixWitnessN 1 Θ* u* a b W τ p q`
        `= radialCutoff a b (W q p) · heatParametrix 1 Θ* u* τ (W q p)`,                      (def)
  with  `Θ* := vanVleck g`,  `u* := transportCoeff (transportOp (vanVleck g) g gi)`,
        `W  := uniformInverseChart g gi hC hK`.

  KEY STRUCTURAL FACT (the honest layer map).  The Gaussian argument is the CHART IMAGE `W q p`, NOT
  `p`.  So the witness's on-gate formula is `heatParametrix` PULLED BACK through the inverse chart `W`
  and radially cut off — it is NOT a plain `heatParametrix` instance.  Moreover `W 0` fixes the origin
  only POINTWISE (`uniformInverseChart_zero` : `W 0 0 = 0`); it is NOT the identity germ near `0`.
  Consequently J4-285's PLAIN-kernel geometry capstone does not apply verbatim — the residual to close
  L3 is a CHART-COMPOSED geometry capstone (see the firewall below).

  ─────────────────────────────────────────────────────────────────────────────────────────────
  WHAT LANDED (all axiom-free, none the conclusion, none vacuous).
    • (L1) `witness_near_zero_eq_chartParametrix` — the near-`0` POINTWISE germ:
        on the gate (`0∈K`, `z∈S 0`) and the cutoff plateau (`rncRadialSq (W 0 z) ≤ a²`),
          `vanVleckGatedWitness … τ z 0 = heatParametrix 1 Θ* u* τ (W 0 z)`.
      Cutoff `≡1` (`radialCutoff_eq_one`) + gate collapse (`vanVleckGatedWitness_gate_apply`) +
      `heatParametrix_one_apply`.
    • (L2a) `heatOpWitness_eq_heatOp_cutoffChart` — the GATE `heatOp` layer:
        on `Icc t₁ t₂ ×ˢ closedBall 0 R` with `closedBall 0 R ⊆ S 0`, `0∈K`,
          `E = heatOp g gi (globalCutoffParametrixWitnessN 1 Θ* u* a b W) · · 0`.
      A thin wrapper over `ParametrixPartsContinuity.hIdent_gateTransfer` + the witness def.
    • (L2b) `heatOp_cutoffChart_eq_chartParametrix` — the CUTOFF `heatOp` layer:
        where `radialCutoff a b (W 0 ·) ≡ 1` near `z` (a product-open germ; `heatOp` is germ-local via
        `heatOp_congr_nhds`),
          `heatOp g gi (globalCutoffParametrixWitnessN 1 Θ* u* a b W) τ z 0`
            `= heatOp g gi (fun s x _ => heatParametrix 1 Θ* u* s (W 0 x)) τ z 0`.
    • (COMPOSED) `heatOpWitness_eq_chartParametrix_of_gate_cut` — L2a ∘ L2b:
          `E τ z = heatOp g gi (fun s x _ => heatParametrix 1 Θ* u* s (W 0 x)) τ z 0`
      on the gate compact, under the cutoff germ.  The FULL reduction of `E` to the `heatOp` of the
      CHART-COMPOSED order-1 parametrix.
    • (L3, CONDITIONAL) `heatOpGatedWitness_jointContinuousOn_of_chartParametrix` — the joint continuity
      of `E` on `Icc t₁ t₂ ×ˢ closedBall 0 R`, transferred by `ContinuousOn.congr` from the joint
      continuity of the CHART-COMPOSED parametrix kernel `hBcont`, under the pointwise cutoff germ `hcut`.

  ⚠ HONEST FIREWALL.
    THE RESIDUAL (why L3 is conditional, not closed).  `hBcont` is the joint continuity of
      `fun p => heatOp g gi (fun s x _ => heatParametrix 1 Θ* u* s (W 0 x)) p.1 p.2 0`,
    i.e. J4-285 BUT for the kernel `heatParametrix` COMPOSED WITH the inverse chart `x ↦ W 0 x`.  Since
    `W 0` is only origin-fixing pointwise (NOT the identity germ), J4-285's PLAIN-kernel capstone
    (`heatOpWitness_jointContinuousOn_geometry`) does not discharge `hBcont` directly; a genuine
    CHART-COMPOSED geometry capstone is the remaining wall.  `hBcont` is a genuine, satisfiable
    hypothesis (the chart pullback of a jointly-continuous kernel is jointly continuous where `W 0` is
    continuous) and is NOT the conclusion (it is about the chart-parametrix kernel `B`; the conclusion
    is about the witness `E`, linked by the PROVEN reduction).  The cutoff germ `hcut`/`hcut1` is
    likewise genuine and satisfiable: on the near-diagonal plateau `rncRadialSq (W 0 ·) < a²` with
    `W 0` continuous, `radialCutoff a b (W 0 ·) ≡ 1`.

    NONE of this is `a₁ = R/6`.  This file only relocates `E`'s regularity onto the chart-composed
    parametrix; the curvature value is untouched.
-/
import Mathlib
import QIQTH.AmplitudePackage
import QIQTH.ParametrixPartsContinuity
import QIQTH.ConvApproximants

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.HeatParametrixAnsatz QIQTH.LaplaceBeltrami QIQTH.FlatHeatEquation
open QIQTH.ParametrixFunction QIQTH.VanVleck QIQTH.RadialDistance
open QIQTH.HeatTransportRecursion
open QIQTH.ParametrixPartsContinuity
open scoped Topology

namespace QIQTH.GatedWitnessHeatOpBridge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ## (L1) — the near-`0` pointwise germ: witness collapses to the chart-parametrix.
    ############################################################################### -/

/-- **★ (L1) `witness_near_zero_eq_chartParametrix`.**  On the gate (`0 ∈ K`, `z ∈ S 0`) and inside the
    cutoff plateau (`rncRadialSq (W 0 z) ≤ a²`, so `radialCutoff a b (W 0 z) = 1`), the concrete gated
    van-Vleck witness at base point `0` collapses to the order-1 heat parametrix at the CHART IMAGE:
      `vanVleckGatedWitness g gi hC hK S a b τ z 0 = heatParametrix 1 Θ* u* τ (W 0 z)`,
    with `Θ* = vanVleck g`, `u* = transportCoeff (transportOp (vanVleck g) g gi)`,
    `W = uniformInverseChart g gi hC hK`.  Pure def-chain: `vanVleckGatedWitness_gate_apply` +
    `radialCutoff_eq_one` + `heatParametrix_one_apply`.  Genuine carries (`0 < a < b`, gate memberships,
    plateau); none is the conclusion.  NOT `a₁ = R/6`. -/
theorem witness_near_zero_eq_chartParametrix (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b τ : ℝ)
    (ha : 0 < a) (hab : a < b)
    {z : Point n} (h0K : (0 : Point n) ∈ K) (hzS : z ∈ S 0)
    (hcut : rncRadialSq (uniformInverseChart g gi hC hK 0 z) ≤ a ^ 2) :
    vanVleckGatedWitness g gi hC hK S a b τ z 0
      = heatParametrix 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) τ
          (uniformInverseChart g gi hC hK 0 z) := by
  rw [vanVleckGatedWitness_gate_apply g gi hC hK S a b τ h0K hzS,
      radialCutoff_eq_one ha hab hcut, one_mul, heatParametrix_one_apply]

/-! ###############################################################################
    ## (L2a) — the GATE `heatOp` layer.
    ############################################################################### -/

/-- **★ (L2a) `heatOpWitness_eq_heatOp_cutoffChart`.**  On the positive-time compact
    `Icc t₁ t₂ ×ˢ closedBall 0 R` with the closedBall INSIDE the open gate `S 0` (and `0 ∈ K`), the gated
    witness's heat operator equals the UNGATED cutoff-chart parametrix's:
      `heatOp g gi (vanVleckGatedWitness …) p.1 p.2 0`
        `= heatOp g gi (globalCutoffParametrixWitnessN 1 Θ* u* a b W) p.1 p.2 0`.
    A thin specialization of `ParametrixPartsContinuity.hIdent_gateTransfer` at
    `H := globalCutoffParametrixWitnessN 1 Θ* u* a b W` — `vanVleckGatedWitness … = gatedKernel K S H`
    by definition.  Genuine carries (gate openness/containment, `0∈K`); none is the conclusion.
    NOT `a₁ = R/6`. -/
theorem heatOpWitness_eq_heatOp_cutoffChart (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t₁ t₂ R : ℝ) (h0K : (0 : Point n) ∈ K) (hSopen : IsOpen (S 0))
    (hsub : Metric.closedBall (0 : Point n) R ⊆ S 0) :
    ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R,
      heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 0
        = heatOp g gi (globalCutoffParametrixWitnessN 1 (vanVleck g)
            (transportCoeff (transportOp (vanVleck g) g gi)) a b
            (uniformInverseChart g gi hC hK)) p.1 p.2 0 := by
  intro p hp
  exact hIdent_gateTransfer g gi K S
    (globalCutoffParametrixWitnessN 1 (vanVleck g)
      (transportCoeff (transportOp (vanVleck g) g gi)) a b
      (uniformInverseChart g gi hC hK))
    t₁ t₂ R h0K hSopen hsub p hp

/-! ###############################################################################
    ## (L2b) — the CUTOFF `heatOp` layer.
    ############################################################################### -/

/-- **★ (L2b) `heatOp_cutoffChart_eq_chartParametrix`.**  Where the radial cutoff of the chart image is
    identically `1` near `z` (`hcut1`, a product-open — `τ`-independent — germ), the `heatOp` of the
    cutoff-chart parametrix agrees with the `heatOp` of the PURE chart-composed parametrix at `(τ,z,0)`:
      `heatOp g gi (globalCutoffParametrixWitnessN 1 Θ* u* a b W) τ z 0`
        `= heatOp g gi (fun s x _ => heatParametrix 1 Θ* u* s (W 0 x)) τ z 0`.
    `heatOp` is germ-local (`GlobalHunifAssembly.heatOp_congr_nhds`): the time germ holds for ALL `t`
    (cutoff `τ`-independent, value `1` at `z`), the space germ on the plateau neighborhood `hcut1`.
    The germ `hcut1` is genuine/satisfiable (continuity of `W 0` at `z` + strict plateau); not the
    conclusion.  NOT `a₁ = R/6`. -/
theorem heatOp_cutoffChart_eq_chartParametrix (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b τ : ℝ)
    {z : Point n}
    (hcut1 : (fun p' : Point n => radialCutoff a b (uniformInverseChart g gi hC hK 0 p'))
      =ᶠ[nhds z] (fun _ => (1 : ℝ))) :
    heatOp g gi (globalCutoffParametrixWitnessN 1 (vanVleck g)
        (transportCoeff (transportOp (vanVleck g) g gi)) a b
        (uniformInverseChart g gi hC hK)) τ z 0
      = heatOp g gi (fun s x (_ : Point n) => heatParametrix 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) s
          (uniformInverseChart g gi hC hK 0 x)) τ z 0 := by
  refine heatOp_congr_nhds g gi _ _ τ z 0 ?_ ?_
  · -- time germ (at fixed `p = z`): the cutoff is `1` at `z` for ALL times `t`.
    have h1 : radialCutoff a b (uniformInverseChart g gi hC hK 0 z) = 1 := hcut1.self_of_nhds
    refine Filter.Eventually.of_forall (fun t => ?_)
    simp only [globalCutoffParametrixWitnessN, h1, one_mul]
  · -- space germ (at fixed time `τ`): the cutoff is `1` on the plateau neighborhood `hcut1`.
    filter_upwards [hcut1] with p' hp'
    have hp'1 : radialCutoff a b (uniformInverseChart g gi hC hK 0 p') = 1 := hp'
    simp only [globalCutoffParametrixWitnessN, hp'1, one_mul]

/-! ###############################################################################
    ## (COMPOSED) — full reduction of `E` to the chart-composed parametrix `heatOp`.
    ############################################################################### -/

/-- **★★ (COMPOSED) `heatOpWitness_eq_chartParametrix_of_gate_cut`.**  L2a ∘ L2b: on the gate compact
    (`0∈K`, `S 0` open, `closedBall 0 R ⊆ S 0`) and under the near-diagonal cutoff germ `hcut1`, the
    concrete gated-witness heat operator EQUALS the heat operator of the CHART-COMPOSED order-1
    parametrix at `(p.1, p.2, 0)`:
      `heatOp g gi (vanVleckGatedWitness …) p.1 p.2 0`
        `= heatOp g gi (fun s x _ => heatParametrix 1 Θ* u* s (W 0 x)) p.1 p.2 0`.
    NOT `a₁ = R/6`. -/
theorem heatOpWitness_eq_chartParametrix_of_gate_cut (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t₁ t₂ R : ℝ) (h0K : (0 : Point n) ∈ K) (hSopen : IsOpen (S 0))
    (hsub : Metric.closedBall (0 : Point n) R ⊆ S 0)
    (p : ℝ × Point n) (hp : p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)
    (hcut1 : (fun p' : Point n => radialCutoff a b (uniformInverseChart g gi hC hK 0 p'))
      =ᶠ[nhds p.2] (fun _ => (1 : ℝ))) :
    heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 0
      = heatOp g gi (fun s x (_ : Point n) => heatParametrix 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) s
          (uniformInverseChart g gi hC hK 0 x)) p.1 p.2 0 := by
  rw [heatOpWitness_eq_heatOp_cutoffChart g gi hC hK S a b t₁ t₂ R h0K hSopen hsub p hp]
  exact heatOp_cutoffChart_eq_chartParametrix g gi hC hK a b p.1 hcut1

/-! ###############################################################################
    ## (L3, CONDITIONAL) — joint continuity of `E`, modulo the chart-composed capstone.
    ############################################################################### -/

/-- **★★ (L3, CONDITIONAL) `heatOpGatedWitness_jointContinuousOn_of_chartParametrix`.**  The joint
    `(τ,z)`-continuity of the concrete gated-witness heat operator
      `E := fun p => heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 0`
    on `Icc t₁ t₂ ×ˢ closedBall 0 R`, transferred by `ContinuousOn.congr` (through the COMPOSED
    reduction) from:
      • `hBcont` — the joint continuity of the CHART-COMPOSED order-1 parametrix heat operator
        `fun p => heatOp g gi (fun s x _ => heatParametrix 1 Θ* u* s (W 0 x)) p.1 p.2 0`
        (= J4-285 for the chart-pulled-back kernel; the remaining wall, NOT the conclusion), and
      • `hcut` — the pointwise near-diagonal cutoff germ over the compact.
    Both carries are genuine and satisfiable (see the firewall); neither is the conclusion.
    NOT `a₁ = R/6`. -/
theorem heatOpGatedWitness_jointContinuousOn_of_chartParametrix (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (t₁ t₂ R : ℝ) (h0K : (0 : Point n) ∈ K) (hSopen : IsOpen (S 0))
    (hsub : Metric.closedBall (0 : Point n) R ⊆ S 0)
    (hcut : ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R,
      (fun p' : Point n => radialCutoff a b (uniformInverseChart g gi hC hK 0 p'))
        =ᶠ[nhds p.2] (fun _ => (1 : ℝ)))
    (hBcont : ContinuousOn (fun p : ℝ × Point n =>
        heatOp g gi (fun s x (_ : Point n) => heatParametrix 1 (vanVleck g)
          (transportCoeff (transportOp (vanVleck g) g gi)) s
          (uniformInverseChart g gi hC hK 0 x)) p.1 p.2 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  refine hBcont.congr (fun p hp => ?_)
  exact heatOpWitness_eq_chartParametrix_of_gate_cut g gi hC hK S a b t₁ t₂ R
    h0K hSopen hsub p hp (hcut p hp)

#check @witness_near_zero_eq_chartParametrix
#check @heatOpWitness_eq_heatOp_cutoffChart
#check @heatOp_cutoffChart_eq_chartParametrix
#check @heatOpWitness_eq_chartParametrix_of_gate_cut
#check @heatOpGatedWitness_jointContinuousOn_of_chartParametrix

end QIQTH.GatedWitnessHeatOpBridge

/-! ## Axiom checks — every theorem `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.GatedWitnessHeatOpBridge
#print axioms witness_near_zero_eq_chartParametrix
#print axioms heatOpWitness_eq_heatOp_cutoffChart
#print axioms heatOp_cutoffChart_eq_chartParametrix
#print axioms heatOpWitness_eq_chartParametrix_of_gate_cut
#print axioms heatOpGatedWitness_jointContinuousOn_of_chartParametrix
end AxiomChecks
