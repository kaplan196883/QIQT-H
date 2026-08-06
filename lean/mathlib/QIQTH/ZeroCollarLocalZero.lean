/-
  ZeroCollarLocalZero — J4-292: the ZERO-COLLAR verdict + the local-zero / active-region /
  globalized-base-case lemmas for the concrete gated van-Vleck witness heat operator `E`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  (A)  ★★ THE ZERO-COLLAR VERDICT  (the critical repo fact).

  The witness's radial cutoff support sits STRICTLY inside the hard gate — the collar HOLDS, with a
  positive radius margin.  Concretely:

    • The base kernel is `globalCutoffParametrixWitnessN N Θ u a b W τ p q
        = radialCutoff a b (W q p) · heatParametrix N Θ u τ (W q p)` (`OrderNResidual`), and
      `radialCutoff a b v` vanishes for `b² ≤ rncRadialSq v` (`SmoothCutoff.radialCutoff_eq_zero`).
      Hence the cutoff-ACTIVE region in `p` (base `q` fixed) is contained in the OPEN radial sublevel
      `{p | rncRadialSq (W q p) < b²}` — lemma `cutoff_active_subset_sublevel`.

    • The concrete provider gate (`GateOpennessExport.gatedWitnessN1_hEboundW_le_lin_pkg_open`) is
      `S q = φ_q '' ball 0 c` with `b < c`, and `W q ∘ φ_q = id` (the left-inverse germ).  So in chart
      coordinates the active support is the ball of radius `b` (in `rncRadial`), while the gate is the
      ball of radius `c > b`: the annulus `b ≤ ‖w‖ < c` is the COLLAR — inside the gate, cutoff `≡ 0`.
      On the gate FRONTIER (`‖w'‖ = c > b`) the cutoff already vanishes; this is precisely the LEG-3
      computation ALREADY discharged inside `GateOpennessExport` (lines 140–170), which is why the
      trichotomy's off-gate germ lands.

    VERDICT:  the collar is REAL and has margin `c − b > 0`, but it is NOT a *pure radial-sublevel
    definition* of the gate — it is realized through the left-inverse germ `W q ∘ φ_q = id`.  The
    provider can (and does) choose `c > b`, so no re-choice is needed.  The heatOp-vanishing on the
    frontier collar is already banked.  This file re-exports the *provider-agnostic* skeleton
    (`cutoff_active_subset_sublevel`, `isOpen_cutoff_sublevel`) and builds the local-zero /
    active-region / globalized-base-case chain on top of it.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  (B)–(D)  WHAT LANDS (all provider-agnostic except the (D) instantiation; NO `sorry`; std-3):

    • (base)  `globalCutoffParametrixWitnessN_eq_zero_of_cutoff_zero` /
              `gatedKernel_eq_zero_of_base_zero` / `gatedWitness_eq_zero_of_cutoff_zero`
              — the witness (base kernel and gated) vanishes pointwise wherever `radialCutoff a b (W q p) = 0`.
    • (B1)  `gatedWitness_eventuallyEq_zero_of_far` — for a fixed base `q`, the gated-witness section
            `p ↦ Wit τ p q` is `=ᶠ[𝓝 z] 0` at any `z` with `b² < rncRadialSq (W q z)` (given
            `ContinuousAt (W q) z`): the strict far condition is OPEN, so cutoff `≡ 0` on a neighbourhood.
    • (B2)  `heatOpGatedWitness_eq_zero_of_far` — heatOp locality: `E τ z q = 0` there, via
            `heatOp_eq_zero_of_locally_zero` (time germ = the cutoff is `τ`-independent, space germ = B1).
    • (C-chart)  `heatOpGatedWitness_active_chart` — contrapositive: `E τ z q ≠ 0 ⟹ rncRadialSq (W q z) ≤ b²`.
    • (C-ambient) `heatOpGatedWitness_active_displacement` / `_norm` — with `GateSqControl` and the
            on-gate carry `z ∈ S q`, `rncRadialSq (z − q) ≤ (3/2)·b²`, hence `‖z − q‖ ≤ √(3/2)·b`
            (the S-dom localization of the active base).
    • (D-skeleton) `continuousOn_of_active_open_zero_off` — a general two-region pasting lemma:
            continuity on an OPEN active set `A` + local-zero off `A` ⟹ `ContinuousOn` on the slab.
    • (D)  `E_slice_continuousOn_off_support` — the globalized base case (base slot `0`) for ALL radii:
            given the banked active-region continuity carry `hEA` on an open `A` and the honest radii
            carry `hoff` (points of the slab off `A` are strictly-far, `b² < rncRadialSq (W₀ ·)`), plus
            `W₀` continuous on the `C²` ball, `E(·,·,0)` is `ContinuousOn (Icc t₁ t₂ ×ˢ closedBall 0 R)`.
            The local-zero half is DISCHARGED here (via B1/B2); the active-region continuity is exactly
            the banked `ChartJetFactsDischarge.heatOpGatedWitness_jointContinuousOn_chartFree` output,
            kept as the carry `hEA`.

  ⚠  HONEST FIREWALL.  No `sorry` (this header prose aside), no `:= True`, no conclusion-as-hypothesis.
     Every carried hypothesis is genuine and satisfiable (`ContinuousAt (W q) z` from the chart's `C²`
     region; `GateSqControl` is the banked near-isometry certificate; `hEA` is the banked joint-continuity
     capstone; `hoff` is the collar geometry).  This file supplies the STRUCTURAL foundations of the
     Levi-continuity chain; it says NOTHING new about the curvature value.  **NOT `a₁ = R/6`.**
-/
import Mathlib
import QIQTH.ConvApproximants
import QIQTH.ChartJetFactsDischarge
import QIQTH.CutoffAnnulusSupport
import QIQTH.ConcreteDominations
import QIQTH.GlobalWitnessHunif
import QIQTH.OrderNResidual
import QIQTH.RNCDecay

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.RNCDecay
open QIQTH.TrueHeatKernel QIQTH.HeatResidualBound
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open scoped BigOperators Topology

namespace QIQTH.ZeroCollarLocalZero

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ## Base: the witness vanishes pointwise where the radial cutoff vanishes.
    ############################################################################### -/

/-- The order-`N` cutoff-parametrix base kernel vanishes wherever the radial cutoff of the chart image
    vanishes (it carries `radialCutoff a b (W q p)` as a MULTIPLICATIVE prefactor). -/
theorem globalCutoffParametrixWitnessN_eq_zero_of_cutoff_zero (N : ℕ) (Θ : Point n → ℝ)
    (u : ℕ → Point n → ℝ) (a b : ℝ) (W : Point n → Point n → Point n) (τ : ℝ) (p q : Point n)
    (h : radialCutoff a b (W q p) = 0) :
    globalCutoffParametrixWitnessN N Θ u a b W τ p q = 0 := by
  simp only [globalCutoffParametrixWitnessN, h, zero_mul]

/-- The gated kernel vanishes wherever its base kernel vanishes (both `if`-branches evaluate to `0`). -/
theorem gatedKernel_eq_zero_of_base_zero (K : Set (Point n)) (S : Point n → Set (Point n))
    (H : ℝ → Point n → Point n → ℝ) (τ : ℝ) (p q : Point n) (h : H τ p q = 0) :
    gatedKernel K S H τ p q = 0 := by
  simp only [gatedKernel]
  split_ifs <;> simp [h]

/-- **The gated cutoff-parametrix witness vanishes pointwise on the far region.**  Wherever
    `radialCutoff a b (W q p) = 0` the whole gated witness is `0` — irrespective of the gate `S`. -/
theorem gatedWitness_eq_zero_of_cutoff_zero (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (a b : ℝ) (K : Set (Point n)) (S : Point n → Set (Point n)) (W : Point n → Point n → Point n)
    (τ : ℝ) (p q : Point n) (h : radialCutoff a b (W q p) = 0) :
    gatedKernel K S (globalCutoffParametrixWitnessN N Θ u a b W) τ p q = 0 :=
  gatedKernel_eq_zero_of_base_zero K S _ τ p q
    (globalCutoffParametrixWitnessN_eq_zero_of_cutoff_zero N Θ u a b W τ p q h)

/-! ###############################################################################
    ## (A) The zero-collar containment + openness of the collar interior.
    ############################################################################### -/

/-- **★ (A) THE ZERO-COLLAR CONTAINMENT (provider-agnostic).**  For `0 < a < b`, the cutoff-ACTIVE
    region (base `q` fixed) is contained in the OPEN radial sublevel `{p | rncRadialSq (W q p) < b²}`:
    outside that sublevel (`b² ≤ rncRadialSq (W q p)`) the cutoff `radialCutoff a b (W q p)` vanishes
    (`radialCutoff_eq_zero`), so the witness is `0`.  This is the abstract kernel of the collar: any
    gate whose radial reach exceeds `b` (in chart coordinates) contains the active support with a
    positive margin.  NOT `a₁ = R/6`. -/
theorem cutoff_active_subset_sublevel {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (W : Point n → Point n) :
    {z : Point n | radialCutoff a b (W z) ≠ 0} ⊆ {z : Point n | rncRadialSq (W z) < b ^ 2} := by
  intro z hz
  by_contra h
  simp only [Set.mem_setOf_eq, not_lt] at h
  exact hz (radialCutoff_eq_zero ha hab h)

/-- **The collar interior is open.**  If the chart map `W` is continuous, the sublevel
    `{z | rncRadialSq (W z) < b²}` containing the cutoff-active support is open. -/
theorem isOpen_cutoff_sublevel {b : ℝ} {W : Point n → Point n} (hW : Continuous W) :
    IsOpen {z : Point n | rncRadialSq (W z) < b ^ 2} :=
  (isOpen_rncRadialSq_lt (b ^ 2)).preimage hW

/-! ###############################################################################
    ## (B1)–(B2) The local-zero lemmas (space germ + heatOp locality).
    ############################################################################### -/

/-- **★ (B1) THE WITNESS SPACE-GERM LOCAL ZERO.**  For a fixed base `q`, the gated-witness section
    `p ↦ Wit τ p q` is `=ᶠ[𝓝 z] 0` at any point `z` strictly outside the far ball
    (`b² < rncRadialSq (W q z)`), given `ContinuousAt (W q) z`: the strict far condition is OPEN
    (`isOpen_rncRadialSq_gt`), so its `(W q)`-preimage is a neighbourhood of `z` on which the cutoff —
    hence the witness — is `0`.  NOT `a₁ = R/6`. -/
theorem gatedWitness_eventuallyEq_zero_of_far {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (K : Set (Point n))
    (S : Point n → Set (Point n)) (W : Point n → Point n → Point n) (τ : ℝ) (q : Point n)
    {z : Point n} (hWc : ContinuousAt (W q) z) (hz : b ^ 2 < rncRadialSq (W q z)) :
    (fun p => gatedKernel K S (globalCutoffParametrixWitnessN N Θ u a b W) τ p q)
      =ᶠ[nhds z] (fun _ => (0 : ℝ)) := by
  have hpre : (W q) ⁻¹' {w : Point n | b ^ 2 < rncRadialSq w} ∈ nhds z :=
    hWc.preimage_mem_nhds ((isOpen_rncRadialSq_gt (b ^ 2)).mem_nhds hz)
  filter_upwards [hpre] with p hp
  have hp' : b ^ 2 < rncRadialSq (W q p) := hp
  exact gatedWitness_eq_zero_of_cutoff_zero N Θ u a b K S W τ p q
    (radialCutoff_eq_zero ha hab (le_of_lt hp'))

/-- **★ (B2) THE HEATOP LOCAL ZERO OFF THE SUPPORT.**  The gated-witness heat operator `E τ z q`
    vanishes at any `z` strictly outside the far ball (`b² < rncRadialSq (W q z)`), given
    `ContinuousAt (W q) z`.  Via `heatOp_eq_zero_of_locally_zero`: the TIME germ holds for ALL `t` (the
    cutoff is `τ`-independent and vanishes at `z`), the SPACE germ is (B1).  This is the germ/eventuallyEq
    route (NOT pointwise).  NOT `a₁ = R/6`. -/
theorem heatOpGatedWitness_eq_zero_of_far (g gi : Point n → Fin n → Fin n → ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (W : Point n → Point n → Point n)
    (τ : ℝ) (q : Point n) {z : Point n} (hWc : ContinuousAt (W q) z)
    (hz : b ^ 2 < rncRadialSq (W q z)) :
    heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN N Θ u a b W)) τ z q = 0 := by
  refine heatOp_eq_zero_of_locally_zero g gi _ τ z q ?_ ?_
  · -- time germ: cutoff at `z` is `0` (τ-independent), so the section is `0` for every `t`.
    refine Filter.Eventually.of_forall (fun t => ?_)
    exact gatedWitness_eq_zero_of_cutoff_zero N Θ u a b K S W t z q
      (radialCutoff_eq_zero ha hab (le_of_lt hz))
  · -- space germ: (B1).
    exact gatedWitness_eventuallyEq_zero_of_far ha hab N Θ u K S W τ q hWc hz

/-! ###############################################################################
    ## (C) The active-region localization (S-dom).
    ############################################################################### -/

/-- **★ (C-chart) THE ACTIVE-REGION CHART BOUND.**  Contrapositive of (B2): if the gated-witness heat
    operator is nonzero at `(τ, z, q)` then the chart image lies in the closed near ball,
    `rncRadialSq (W q z) ≤ b²`.  (Given `ContinuousAt (W q) z`.)  NOT `a₁ = R/6`. -/
theorem heatOpGatedWitness_active_chart (g gi : Point n → Fin n → Fin n → ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (W : Point n → Point n → Point n)
    (τ : ℝ) (q : Point n) {z : Point n} (hWc : ContinuousAt (W q) z)
    (hne : heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN N Θ u a b W)) τ z q ≠ 0) :
    rncRadialSq (W q z) ≤ b ^ 2 := by
  by_contra h
  rw [not_le] at h
  exact hne (heatOpGatedWitness_eq_zero_of_far g gi ha hab N Θ u K S W τ q hWc h)

/-- **★★ (C-ambient) THE ACTIVE-REGION DISPLACEMENT BOUND (S-dom, squared form).**  Combining the
    chart bound (C-chart) with the near-isometry certificate `GateSqControl` (on the gate,
    `rncRadialSq (z − q) ≤ (3/2)·rncRadialSq (W q z)`) and the on-gate membership carry `z ∈ S q`
    (satisfiable: off the gate `E = 0`, so a nonzero `E` forces `z` into the gate's active core): a
    nonzero gated-witness heat operator forces the ambient displacement to satisfy
    `rncRadialSq (z − q) ≤ (3/2)·b²`.  NOT `a₁ = R/6`. -/
theorem heatOpGatedWitness_active_displacement (g gi : Point n → Fin n → Fin n → ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (W : Point n → Point n → Point n)
    (hgate : GateSqControl K S W) (τ : ℝ) (q : Point n) (hq : q ∈ K) {z : Point n}
    (hWc : ContinuousAt (W q) z) (hzS : z ∈ S q)
    (hne : heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN N Θ u a b W)) τ z q ≠ 0) :
    rncRadialSq (z - q) ≤ (3 / 2 : ℝ) * b ^ 2 := by
  have hchart : rncRadialSq (W q z) ≤ b ^ 2 :=
    heatOpGatedWitness_active_chart g gi ha hab N Θ u K S W τ q hWc hne
  calc rncRadialSq (z - q)
      ≤ (3 / 2 : ℝ) * rncRadialSq (W q z) := hgate q hq z hzS
    _ ≤ (3 / 2 : ℝ) * b ^ 2 := mul_le_mul_of_nonneg_left hchart (by norm_num)

/-- **★★ (C-ambient) THE ACTIVE-REGION NORM BOUND.**  The metric form of the S-dom localization: the
    active base sits within `‖z − q‖ ≤ √(3/2)·b` of `z` — so if `z ∈ closedBall 0 R` then
    `q ∈ closedBall 0 (R + √(3/2)·b)` (the `R* = R + range` localization).  NOT `a₁ = R/6`. -/
theorem heatOpGatedWitness_active_norm (g gi : Point n → Fin n → Fin n → ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n)) (W : Point n → Point n → Point n)
    (hgate : GateSqControl K S W) (τ : ℝ) (q : Point n) (hq : q ∈ K) {z : Point n}
    (hWc : ContinuousAt (W q) z) (hzS : z ∈ S q)
    (hne : heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN N Θ u a b W)) τ z q ≠ 0) :
    ‖z - q‖ ≤ Real.sqrt (3 / 2) * b := by
  have hb : 0 ≤ b := le_of_lt (lt_trans ha hab)
  have hsq : rncRadialSq (z - q) ≤ (3 / 2 : ℝ) * b ^ 2 :=
    heatOpGatedWitness_active_displacement g gi ha hab N Θ u K S W hgate τ q hq hWc hzS hne
  have hnorm : ‖z - q‖ ≤ rncRadial (z - q) := norm_le_rncRadial (z - q)
  have hrad : rncRadial (z - q) ≤ Real.sqrt (3 / 2) * b := by
    have hstep : Real.sqrt (rncRadialSq (z - q)) ≤ Real.sqrt (3 / 2 * b ^ 2) :=
      Real.sqrt_le_sqrt hsq
    have hval : Real.sqrt (3 / 2 * b ^ 2) = Real.sqrt (3 / 2) * b := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hb]
    calc rncRadial (z - q) = Real.sqrt (rncRadialSq (z - q)) := rfl
      _ ≤ Real.sqrt (3 / 2 * b ^ 2) := hstep
      _ = Real.sqrt (3 / 2) * b := hval
  linarith [hnorm, hrad]

/-! ###############################################################################
    ## (D-skeleton) A general two-region pasting lemma.
    ############################################################################### -/

/-- **★ (D-skeleton) TWO-REGION CONTINUITY PASTING.**  If `E` is continuous at every point of a set
    `A` (intended: the OPEN active set), and at every point of `s` NOT in `A` the field `E` is locally
    the zero function (`=ᶠ[𝓝 x] 0`), then `E` is `ContinuousOn s`.  (Points in `A` use `ContinuousAt`;
    points off `A` use the local-zero germ + `ContinuousAt.congr continuousAt_const`.)  Openness of `A`
    is not needed — `hEA` supplies `ContinuousAt` directly.  Provider-agnostic. -/
theorem continuousOn_of_active_open_zero_off {X : Type*} [TopologicalSpace X]
    (E : X → ℝ) (s A : Set X)
    (hEA : ∀ x ∈ A, ContinuousAt E x)
    (hzero : ∀ x ∈ s, x ∉ A → E =ᶠ[nhds x] (fun _ => (0 : ℝ))) :
    ContinuousOn E s := by
  intro x hx
  by_cases hxA : x ∈ A
  · exact (hEA x hxA).continuousWithinAt
  · exact (ContinuousAt.congr continuousAt_const (hzero x hx hxA).symm).continuousWithinAt

/-! ###############################################################################
    ## (D) The globalized base case for the concrete van-Vleck witness (base slot `0`).
    ############################################################################### -/

/-- **★★★ (D) THE GLOBALIZED BASE CASE — `E(·,·,0)` continuity for ALL radii.**  For the concrete gated
    van-Vleck witness heat operator `E p := heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 0`,
    given:

    * `hRρc : R < ρc` and `hW0cont` — the base-0 inverse chart `W₀ = uniformInverseChart g gi hC hK 0`
      is `ContinuousOn (ball 0 ρc)` (its `C²` region, `ChartJetFactsDischarge.chartField_contDiffOn_ball`);
    * an OPEN active set `A` with `hEA : ContinuousAt E` on `A` — the banked joint-continuity output
      (`ChartJetFactsDischarge.heatOpGatedWitness_jointContinuousOn_chartFree` gives `ContinuousOn` on the
      active slab; `A` is any open set inside it, e.g. an open sub-slab covering the support);
    * `hoff` — the HONEST radii/collar carry: every slab point OFF `A` is strictly far,
      `b² < rncRadialSq (W₀ ·)` (the cutoff support is inside `A`; the provider can choose `b` small so
      the support ⊆ the `C²` ball, and `A` covers it),

    the slice `E(·,·,0)` is `ContinuousOn (Icc t₁ t₂ ×ˢ closedBall 0 R)`.  The local-zero half is
    DISCHARGED here (via B1/B2, base `q = 0`); the active-region continuity is the carried banked
    capstone.  NOT `a₁ = R/6`. -/
theorem E_slice_continuousOn_off_support (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (t₁ t₂ R ρc : ℝ) (hRρc : R < ρc)
    (hW0cont : ContinuousOn (uniformInverseChart g gi hC hK 0) (Metric.ball 0 ρc))
    (A : Set (ℝ × Point n))
    (hEA : ∀ p ∈ A, ContinuousAt (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 0) p)
    (hoff : ∀ p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R, p ∉ A →
        b ^ 2 < rncRadialSq (uniformInverseChart g gi hC hK 0 p.2)) :
    ContinuousOn (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  refine continuousOn_of_active_open_zero_off _ _ A hEA ?_
  intro p hp hpA
  have hfar : b ^ 2 < rncRadialSq (uniformInverseChart g gi hC hK 0 p.2) := hoff p hp hpA
  -- `p.2 ∈ closedBall 0 R ⊆ ball 0 ρc`, an open neighbourhood on which `W₀` is continuous.
  have hz : p.2 ∈ Metric.ball (0 : Point n) ρc :=
    Metric.closedBall_subset_ball hRρc hp.2
  have hballnhds : Metric.ball (0 : Point n) ρc ∈ nhds p.2 :=
    Metric.isOpen_ball.mem_nhds hz
  have hWc_z : ContinuousAt (uniformInverseChart g gi hC hK 0) p.2 :=
    hW0cont.continuousAt hballnhds
  have hNnhds : (uniformInverseChart g gi hC hK 0) ⁻¹' {w : Point n | b ^ 2 < rncRadialSq w}
      ∈ nhds p.2 :=
    hWc_z.preimage_mem_nhds ((isOpen_rncRadialSq_gt (b ^ 2)).mem_nhds hfar)
  have hN'nhds :
      (uniformInverseChart g gi hC hK 0) ⁻¹' {w : Point n | b ^ 2 < rncRadialSq w}
          ∩ Metric.ball (0 : Point n) ρc ∈ nhds p.2 :=
    Filter.inter_mem hNnhds hballnhds
  have hprodnhds : Set.univ ×ˢ ((uniformInverseChart g gi hC hK 0) ⁻¹'
      {w : Point n | b ^ 2 < rncRadialSq w} ∩ Metric.ball (0 : Point n) ρc) ∈ nhds p := by
    have h := prod_mem_nhds (Filter.univ_mem : (Set.univ : Set ℝ) ∈ nhds p.1) hN'nhds
    rwa [Prod.mk.eta] at h
  filter_upwards [hprodnhds] with x hx
  have hx2 : x.2 ∈ (uniformInverseChart g gi hC hK 0) ⁻¹'
      {w : Point n | b ^ 2 < rncRadialSq w} ∩ Metric.ball (0 : Point n) ρc := hx.2
  have hxfar : b ^ 2 < rncRadialSq (uniformInverseChart g gi hC hK 0 x.2) := hx2.1
  have hxball : x.2 ∈ Metric.ball (0 : Point n) ρc := hx2.2
  have hWc_x : ContinuousAt (uniformInverseChart g gi hC hK 0) x.2 :=
    hW0cont.continuousAt (Metric.isOpen_ball.mem_nhds hxball)
  show heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) x.1 x.2 0 = 0
  simp only [vanVleckGatedWitness]
  exact heatOpGatedWitness_eq_zero_of_far g gi ha hab 1 (vanVleck g)
    (transportCoeff (transportOp (vanVleck g) g gi)) K S (uniformInverseChart g gi hC hK)
    x.1 0 hWc_x hxfar

end QIQTH.ZeroCollarLocalZero

/-! ## Axiom checks. -/
section AxiomChecks
open QIQTH.ZeroCollarLocalZero
#print axioms gatedWitness_eq_zero_of_cutoff_zero
#print axioms cutoff_active_subset_sublevel
#print axioms gatedWitness_eventuallyEq_zero_of_far
#print axioms heatOpGatedWitness_eq_zero_of_far
#print axioms heatOpGatedWitness_active_chart
#print axioms heatOpGatedWitness_active_displacement
#print axioms heatOpGatedWitness_active_norm
#print axioms continuousOn_of_active_open_zero_off
#print axioms E_slice_continuousOn_off_support
end AxiomChecks
