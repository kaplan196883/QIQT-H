/-
  OnGateGlue — J4-373: the ON-GATE GLUE (step 2c of the `AffineGateBound` closure, Sol brick map).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  PACKAGING / TRANSPORT-GLUE brick of the (still CONDITIONAL) `a₁ = R/6` heat-kernel campaign.  It
  glues the banked ON-GATE TRANSPORT IDENTITY
  (`AffineGateTransport.heatOp_globalCutoffWitness_transport`, J4-370) to the parametrix residual on
  the CUTOFF PLATEAU, and promotes the two in-bank carry discharges (`hpt` chart-inverse, `hlap`
  laplaceBeltrami naturality) buried inside the compiled capstone
  `HeatResidualBound.gatedWitnessN1_hEboundW_le_lin` (its lines ~831-852) to standalone lemmas.  NO
  `sorry` (header prose excepted), NO new axioms, NO `:= True`, NO vacuous / unsatisfiable hypothesis,
  NONE equal to (or trivially yielding) the conclusion, NO existing file edited, nothing committed.
  `a₁ = R/6` stays CONDITIONAL on the whole convergence / geometric-wiring stack AND on the surviving
  LABELLED inputs.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE PULLBACK-vs-ORIGINAL METRIC VERDICT (Sol #17, dont-undercredit).  The banked transport
  identity `heatOp_globalCutoffWitness_transport` expresses `heatOp g gi (witness) τ (exp q v) q` as
  the CHART-frame residual `radialCutoff a b v · ∂_τ(heatParametrix …) − Δ_{g̃_q}(radialCutoff·…) v`
  in the PULLBACK metric `g̃_q = uniformFlowPullbackMetric g gi hC hK q`.  On the cutoff PLATEAU
  (`rncRadialSq v < a²`, where `radialCutoff = 1` on a whole nhds of `v`) this collapses — the cutoff
  passes through `∂_τ` (it is a constant `1` in `τ`) AND through `Δ` (via `laplaceBeltrami_congr_nhds`
  on the germ) — to the PULLBACK-metric parametrix residual `parametrixResidualN 1 g̃_q g̃i_q Θ u τ v`.

  ⚠  This is the PULLBACK-metric residual, NOT the ORIGINAL-metric one.  The J4-372 ball leg
  `Transfer43Quad.ambientAffine_onBall` bounds `parametrixResidualN 1 g gi Θ u τ v` in the ORIGINAL
  metric `g gi`; these are DIFFERENT objects (the two `laplaceBeltrami`s use different Christoffels).
  The width-4/3 ENVELOPE composition therefore needs EITHER a pullback-metric analogue of
  `ambientAffine_onBall` OR a pullback↔original residual bridge — NEITHER of which is banked (both would
  be genuine near-isometry-on-the-Laplacian analysis, not a re-wire).  This file therefore banks the
  HONEST glue (`heatOp = pullback-metric residual on the plateau`), which is the true content of
  step 2c, and flags the envelope leg for J4-374.  NOT `a₁ = R/6`.

  ## DELIVERABLES.
  •  (G1) `radialCutoff_eventuallyEq_one` — the OPEN plateau germ (`rncRadialSq v < a²` ⟹
     `radialCutoff a b =ᶠ[𝓝 v] 1`); `cutoffTransport_eq_parametrixResidual` /
     `_onPlateau` — the transport RHS equals the (general-metric) parametrix residual on the plateau.
  •  (G2) `uniformInverseChart_leftInverse_of_lt` — the standalone `hpt` (chart inverse, from the
     banked `uniformInverseChart_huniformChart` germ); `laplaceBeltrami_globalCutoffWitness_naturality`
     — the standalone `hlap` (laplaceBeltrami naturality, from
     `laplaceBeltrami_uniformFlow_naturality_forall_f` + `laplaceBeltrami_congr_nhds`).
  •  (G3) `heatOp_globalCutoffWitness_eq_pullbackResidual_onPlateau` — the GLUE: the witness `heatOp`
     at the exp point equals the pullback-metric parametrix residual on the plateau (transport (2a) ∘
     G1); `gatedKernel_heatOp_eq_pullbackResidual_onPlateau` — the SAME with the hard `q`-set gate in
     front (transparent on the gate interior, via `gatedKernel_heatOp_eq_of_mem_nhds`).

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.AffineGateTransport
import QIQTH.GlobalHunifAssembly

open Finset
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder QIQTH.HeatResidualBound
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped BigOperators ContDiff Topology

namespace QIQTH.OnGateGlue

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (G1) — the cutoff-plateau identification.
    ############################################################################### -/

/-- **★ (G1) — `radialCutoff_eventuallyEq_one`.**  THE OPEN PLATEAU GERM.  On the STRICT inner region
    `rncRadialSq v < a²` (`0 < a < b`) the smooth radial cutoff is identically `1` on a WHOLE
    neighbourhood of `v` — not merely at `v`.  Route: `rncRadialSq` is continuous, so
    `{y | rncRadialSq y < a²}` is open and contains `v`; on it `radialCutoff = 1` by the banked
    `radialCutoff_eq_one`.  This is the germ the `Δ` (laplaceBeltrami) term of the transport RHS needs
    (a pointwise `= 1` does NOT survive a second-order operator).  NOT `a₁ = R/6`. -/
theorem radialCutoff_eventuallyEq_one {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {v : Point n} (hv : rncRadialSq v < a ^ 2) :
    (radialCutoff a b : Point n → ℝ) =ᶠ[nhds v] (fun _ => (1 : ℝ)) := by
  have hcont : Continuous (rncRadialSq : Point n → ℝ) := rncRadialSq_contDiff.continuous
  have hopen : IsOpen {y : Point n | rncRadialSq y < a ^ 2} :=
    isOpen_lt hcont continuous_const
  have hmem : {y : Point n | rncRadialSq y < a ^ 2} ∈ nhds v := hopen.mem_nhds hv
  filter_upwards [hmem] with y hy
  exact radialCutoff_eq_one ha hab (le_of_lt hy)

/-- **★ (G1) — `cutoffTransport_eq_parametrixResidual`.**  THE PLATEAU COLLAPSE (germ form).  For ANY
    metric `(G, Gi)`, GIVEN the pointwise plateau value `hcut : radialCutoff a b v = 1` and the nhds
    germ `hgerm : radialCutoff a b · heatParametrix 1 · =ᶠ[𝓝 v] heatParametrix 1 ·`, the transport RHS
    `radialCutoff a b v · ∂_τ(heatParametrix 1 · v) − Δ_G(radialCutoff a b · · heatParametrix 1 τ ·) v`
    EQUALS the parametrix residual `parametrixResidualN 1 G Gi Θ u τ v`.  Route: `hcut` + `one_mul`
    drops the cutoff from the `∂_τ` term (constant `1` in `τ`); `laplaceBeltrami_congr_nhds` on `hgerm`
    drops it from the `Δ` term.  NEITHER hypothesis equals the conclusion.  NOT `a₁ = R/6`. -/
theorem cutoffTransport_eq_parametrixResidual
    (G Gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (a b : ℝ) (v : Point n) {τ : ℝ}
    (hcut : radialCutoff a b v = 1)
    (hgerm : (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y)
        =ᶠ[nhds v] (fun y => heatParametrix 1 Θ u τ y)) :
    radialCutoff a b v * deriv (fun s => heatParametrix 1 Θ u s v) τ
        - laplaceBeltrami G Gi (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v
      = parametrixResidualN 1 G Gi Θ u τ v := by
  rw [parametrixResidualN, hcut, one_mul,
    QIQTH.VanVleckCancellation.laplaceBeltrami_congr_nhds G Gi
      (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y)
      (fun y => heatParametrix 1 Θ u τ y) v hgerm]

/-- **★ (G1) — `cutoffTransport_eq_parametrixResidual_onPlateau`.**  THE PLATEAU COLLAPSE (radius form).
    Same as `cutoffTransport_eq_parametrixResidual` but with the germ + pointwise value DERIVED
    internally from the single STRICT plateau condition `rncRadialSq v < a²` (`0 < a < b`).  NOT
    `a₁ = R/6`. -/
theorem cutoffTransport_eq_parametrixResidual_onPlateau
    (G Gi : Point n → Fin n → Fin n → ℝ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {τ : ℝ} {v : Point n}
    (hv : rncRadialSq v < a ^ 2) :
    radialCutoff a b v * deriv (fun s => heatParametrix 1 Θ u s v) τ
        - laplaceBeltrami G Gi (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v
      = parametrixResidualN 1 G Gi Θ u τ v := by
  have hcut : radialCutoff a b v = 1 := radialCutoff_eq_one ha hab (le_of_lt hv)
  have hone := radialCutoff_eventuallyEq_one ha hab hv
  have hgerm : (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y)
      =ᶠ[nhds v] (fun y => heatParametrix 1 Θ u τ y) := by
    filter_upwards [hone] with y hy
    rw [hy, one_mul]
  exact cutoffTransport_eq_parametrixResidual G Gi Θ u a b v hcut hgerm

/-! ###############################################################################
    ### (G2) — the standalone carry discharges (`hpt`, `hlap`).
    ############################################################################### -/

/-- **★ (G2) — `uniformInverseChart_leftInverse_of_lt`.**  THE STANDALONE `hpt` (chart inverse).  On a
    SINGLE radius `δ₀ > 0` over `K`, the uniform inverse chart is a genuine left inverse of the uniform
    flow-exp at every base point `q ∈ K` and every source `‖v‖ < δ₀`.  Promoted from the in-bank line
    (CoeffU1Fix:831-832): the banked germ `uniformInverseChart_huniformChart` gives
    `(fun z => W q (exp q z)) =ᶠ[𝓝 v] (fun z => z)`, whose `eq_of_nhds` value is exactly this.  NOT
    `a₁ = R/6`. -/
theorem uniformInverseChart_leftInverse_of_lt (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < δ₀ →
      uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q v) = v := by
  obtain ⟨δ₀, hδ₀, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  refine ⟨δ₀, hδ₀, ?_⟩
  intro q hq v hv
  have hgerm := ((hchart q hq).1 v hv).1
  simpa using hgerm.eq_of_nhds

/-- **★★ (G2) — `laplaceBeltrami_globalCutoffWitness_naturality`.**  THE STANDALONE `hlap`
    (laplaceBeltrami naturality).  On a SINGLE radius `rN > 0` over `K` (the naturality radius),
    GIVEN the honest geometric carries at the exp point (`hg1` metric `C¹`, `hf` witness `C²`, `hU`
    metric nondegeneracy, `hGGi`/`hGiG` two-sided metric inverse) AND the chart germ `hgerm`, the
    ambient-frame laplaceBeltrami of the un-gated `globalCutoffParametrixWitnessN 1` witness at the exp
    point EQUALS the PULLBACK-frame laplaceBeltrami of the cutoff·parametrix profile at `v`.  Promoted
    from the in-bank block (CoeffU1Fix:840-852): `laplaceBeltrami_uniformFlow_naturality_forall_f`
    (naturality) pushed onto the composed profile, then `laplaceBeltrami_congr_nhds` on the chart germ
    (which rewrites `W q (exp q z) = z` inside the witness).  Every carry is SATISFIABLE (all discharged
    in the compiled capstone) and NONE equals the conclusion.  NOT `a₁ = R/6`. -/
theorem laplaceBeltrami_globalCutoffWitness_naturality (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b : ℝ) (τ : ℝ) :
    ∃ rN : ℝ, 0 < rN ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < rN →
      (∀ a' b', ContDiffAt ℝ 1 (fun y => g y a' b') (uniformFlowExp g gi hC hK q v)) →
      ContDiffAt ℝ 2
          (fun x => globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hC hK) τ x q)
          (uniformFlowExp g gi hC hK q v) →
      IsUnit (matToCLM (fun a' b' => g (uniformFlowExp g gi hC hK q v) a' b')) →
      (∀ pp cc, (∑ bb, g (uniformFlowExp g gi hC hK q v) pp bb
          * gi (uniformFlowExp g gi hC hK q v) bb cc) = if pp = cc then (1 : ℝ) else 0) →
      (∀ pp cc, (∑ aa, gi (uniformFlowExp g gi hC hK q v) pp aa
          * g (uniformFlowExp g gi hC hK q v) aa cc) = if pp = cc then (1 : ℝ) else 0) →
      (fun z => uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q z))
          =ᶠ[nhds v] (fun z => z) →
      laplaceBeltrami g gi
          (fun p => globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hC hK) τ p q)
          (uniformFlowExp g gi hC hK q v)
        = laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q)
            (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v := by
  obtain ⟨rN, hrNpos, hnat⟩ :=
    laplaceBeltrami_uniformFlow_naturality_forall_f g gi hC hK hgsymm
  refine ⟨rN, hrNpos, ?_⟩
  intro q hq v hvN hg1 hf hU hGGi hGiG hgerm
  have hn := hnat
    (fun x => globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hC hK) τ x q)
    q hq v hvN hg1 hf hU hGGi hGiG
  rw [← hn]
  have hprofilegerm :
      (fun z => globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hC hK) τ
          (uniformFlowExp g gi hC hK q z) q)
        =ᶠ[nhds v] (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) := by
    filter_upwards [hgerm] with z hz
    have hz' : uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q z) = z := hz
    simp only [globalCutoffParametrixWitnessN, hz']
  exact QIQTH.VanVleckCancellation.laplaceBeltrami_congr_nhds
    (uniformFlowPullbackMetric g gi hC hK q) (uniformFlowPullbackMetricInv g gi hC hK q)
    _ _ v hprofilegerm

/-! ###############################################################################
    ### (G3) — the ball-leg glue (transport (2a) ∘ G1), un-gated and gated.
    ############################################################################### -/

/-- **★★ (G3) — `heatOp_globalCutoffWitness_eq_pullbackResidual_onPlateau`.**  THE ON-GATE GLUE
    (un-gated witness).  GIVEN the two transport carries `hpt` (chart inverse — from G2's
    `uniformInverseChart_leftInverse_of_lt`) and `hlap` (naturality — from G2's
    `laplaceBeltrami_globalCutoffWitness_naturality`), on the STRICT cutoff plateau
    `rncRadialSq v < a²` (`0 < a < b`) the un-gated `globalCutoffParametrixWitnessN 1` witness's heat
    operator at the exp point EQUALS the PULLBACK-metric parametrix residual at `v`:
        `heatOp g gi (witness) τ (exp q v) q
            = parametrixResidualN 1 g̃_q g̃i_q Θ u τ v`.
    Route: `heatOp_globalCutoffWitness_transport` (2a) rewrites the LHS to the transport RHS; G1's
    `cutoffTransport_eq_parametrixResidual_onPlateau` collapses it on the plateau.

    ⚠  The residual is in the PULLBACK metric `g̃_q = uniformFlowPullbackMetric g gi hC hK q` — NOT the
    original `g gi`.  The width-4/3 envelope leg (`Transfer43Quad.ambientAffine_onBall`) bounds the
    ORIGINAL-metric residual, a different object; wiring the envelope onto THIS residual needs the
    pullback-metric analogue (J4-374).  NOT `a₁ = R/6`. -/
theorem heatOp_globalCutoffWitness_eq_pullbackResidual_onPlateau
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {τ : ℝ} (q v : Point n)
    (hpt : uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q v) = v)
    (hlap : laplaceBeltrami g gi
          (fun p => globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hC hK) τ p q)
          (uniformFlowExp g gi hC hK q v)
        = laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q)
            (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v)
    (hv : rncRadialSq v < a ^ 2) :
    heatOp g gi (globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hC hK)) τ
        (uniformFlowExp g gi hC hK q v) q
      = parametrixResidualN 1 (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ v := by
  rw [QIQTH.AffineGateTransport.heatOp_globalCutoffWitness_transport g gi hC hK Θ u a b
    (uniformInverseChart g gi hC hK) q v hpt hlap]
  exact cutoffTransport_eq_parametrixResidual_onPlateau
    (uniformFlowPullbackMetric g gi hC hK q) (uniformFlowPullbackMetricInv g gi hC hK q)
    Θ u ha hab hv

/-- **★★ (G3) — `gatedKernel_heatOp_eq_pullbackResidual_onPlateau`.**  THE ON-GATE GLUE (with the hard
    `q`-set gate in front).  The hard set-gate `gatedKernel K S H` is TRANSPARENT on the gate interior:
    where `q ∈ K` and the gate `S q` is a neighbourhood of the exp point, `heatOp` of the gated kernel
    equals `heatOp` of the un-gated `H` (`gatedKernel_heatOp_eq_of_mem_nhds`).  Composing with the
    un-gated glue gives, on the plateau, the SAME pullback-metric residual identity for the GATED
    witness.  The gate-interior hypothesis `hS : S q ∈ 𝓝 (exp q v)` is the honest input a downstream
    capstone supplies from the concrete gate `S = image of a ball under the flow-exp` (per the banked
    `uniformInverseChart_huniformChart` open-image clause); flagged for J4-374.  NOT `a₁ = R/6`. -/
theorem gatedKernel_heatOp_eq_pullbackResidual_onPlateau
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {τ : ℝ} (q v : Point n) (hq : q ∈ K)
    (hS : S q ∈ nhds (uniformFlowExp g gi hC hK q v))
    (hpt : uniformInverseChart g gi hC hK q (uniformFlowExp g gi hC hK q v) = v)
    (hlap : laplaceBeltrami g gi
          (fun p => globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hC hK) τ p q)
          (uniformFlowExp g gi hC hK q v)
        = laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
            (uniformFlowPullbackMetricInv g gi hC hK q)
            (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v)
    (hv : rncRadialSq v < a ^ 2) :
    heatOp g gi (gatedKernel K S
        (globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hC hK))) τ
        (uniformFlowExp g gi hC hK q v) q
      = parametrixResidualN 1 (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u τ v := by
  rw [gatedKernel_heatOp_eq_of_mem_nhds g gi K S
    (globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hC hK)) τ
    (uniformFlowExp g gi hC hK q v) q hq hS]
  exact heatOp_globalCutoffWitness_eq_pullbackResidual_onPlateau g gi hC hK Θ u ha hab q v
    hpt hlap hv

end QIQTH.OnGateGlue

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.OnGateGlue.radialCutoff_eventuallyEq_one
#print axioms QIQTH.OnGateGlue.cutoffTransport_eq_parametrixResidual
#print axioms QIQTH.OnGateGlue.cutoffTransport_eq_parametrixResidual_onPlateau
#print axioms QIQTH.OnGateGlue.uniformInverseChart_leftInverse_of_lt
#print axioms QIQTH.OnGateGlue.laplaceBeltrami_globalCutoffWitness_naturality
#print axioms QIQTH.OnGateGlue.heatOp_globalCutoffWitness_eq_pullbackResidual_onPlateau
#print axioms QIQTH.OnGateGlue.gatedKernel_heatOp_eq_pullbackResidual_onPlateau
