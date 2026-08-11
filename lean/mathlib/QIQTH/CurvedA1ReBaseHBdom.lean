/-
  CurvedA1ReBaseHBdom — J4-603: the RE-BASED `hBdom` (width-2 Levi-series Gaussian domination) at the
  NON-collapsed base compact `K := Metric.closedBall 0 r` (`r > 0`) for the genuinely-curved witness
  `g^K = curvedRNCMetric κ` (`κ < 0`) — the genuine analytic wall the J4-602 audit exposed, SCOPED
  EXACTLY and closed MODULO one precisely-stated missing estimate.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`; this proves NOTHING about the coefficient.  `a₁ = R/6`
  remains CONDITIONAL.  The fat-`K` re-base is the genuine analytic wall; this brick delivers the
  K-GENERICITY VERDICT of the defect-bound producer chain (proved, not prose), the fat-`K` ENGINE
  ASSEMBLY (the entire J4-597 Neumann-tail route factored general-`K` and instantiated at the fat
  ball, conditional on ONE precisely-scoped defect bound), the structural NON-COLLAPSE certificates,
  and the consumption certificate into the general-`K` J4-596 builder.  The missing defect-bound
  PRODUCER at fat `K` is recorded OPEN — that is the point.

  ── ★★ THE K-GENERICITY VERDICT (STEP 1, proved as `rebased_hframeK_unsat`).
  The banked defect-bound producer chain
      `CurvedRNCHeatOpDomPkg.curvedRNC_heatOp_dom_pkg`
        ⟵ `ConstRadiusGateExport.gatedWitnessN1_hEboundW_le_lin_CONST`
        ⟵ `CoeffU1Fix.cutoffResidualN1_uniformFlow_narrow_mixed_below_lin`,
           `CoeffBoundsN1.hCoeffU0_vanVleck`, `CoeffU1Fix.uniformCoeffLinear_bound`
  is K-PARAMETRIC IN FORM (every member binds `{K : Set (Point n)} (hK : IsCompact K)`), but every
  member carries `hframeK : ∀ q ∈ K, g q = δ` — and `hframeK` is LOAD-BEARING PER-`q` all the way
  down (`uniformCoeff_bound`, `uniformFlowPullbackMetricInv_dev_uniform`,
  `uniformFlowChristoffel_linear_decay`, `uniformResidual(_Linear)_gaussian_bound_tau_narrow`): the
  amplitude machinery δ-normalises the uniform-flow pullback metric AT EVERY base point `q ∈ K`
  (RNC-at-`q`), not just at the centre.  For the genuinely-curved witness (`κ ≠ 0`, `n ≥ 2`),
  `hframeK` forces `K ⊆ {0}` (`CurvedA1FintHFarCoercivity.curvedRNCMetric_frame_forces_origin`) —
  so at `K = closedBall 0 r` (`r > 0`) the producer's `hframeK` antecedent PROVABLY FAILS
  (`rebased_hframeK_unsat` below): the J4-597 assembly does NOT re-instantiate at fat `K`, and any
  such "instantiation" would be VACUOUS (the cp466/J4-582 blind spot — checked, not repeated).

  ── THE EXACT MISSING ESTIMATE (scoped, OPEN — the wall).
      (hbound-fat)  ∀ t' τ p q, 0 < τ → τ ≤ t' →
        |heatOp g^κ gi^κ (vanVleckGatedWitness g^κ gi^κ hChr (isCompact_closedBall 0 r)
            (constGate … c) a b) τ p q| ≤ (C·(1+t'))·baseKernelW 2 0 τ p q
  i.e. the all-`t'` width-2 Gaussian defect bound at the FAT base compact.  Its future producer
  requires a CENTER-ONLY-GAUGE rework of the amplitude chain: replace `hframeK` by the centre jets
  `hg0`/`hdg0` PLUS a per-`q` frame-correction (vielbein/Gram normalisation at each `q ∈ K`, with
  `‖g(q) − δ‖ = O(|q|²)` uniform on the ball) through
  `uniformFlowPullbackMetricInv_dev_uniform` / `uniformFlowChristoffel_linear_decay` — the honest
  analytic wall.  Radius interplay for that future producer: the availability radii
  `ρc = min (min rN δ₀) r₁` and `ρ_c = min ρ0 ρ1` are already produced UNIFORMLY over the compact
  `K` (so `r` enters through `K = closedBall 0 r` itself, not as an extra term of the radius `min`);
  the gate radius keeps the prescribed-ceiling joint production `c = (b+ρc)/2 < ε` (J4-599), now
  with the co-instantiated mass-side `hKball : ball 0 rS ⊆ K` satisfied at `rS := r`
  (`CurvedA1ReBase.rebased_ball_subset`) — one shared `K` for both sides.

  ── WHAT LANDS HERE (all proved, std-3; NO sorry, NO `:= True`).
    • `rebased_axis_point` — a genuinely-nonzero point `(r/2)·e₀` of `closedBall 0 r`.
    • `rebased_hframeK_unsat` — ★★ THE VERDICT: the producer chain's `hframeK` antecedent PROVABLY
      FAILS at `K = closedBall 0 r` for the curved witness (`κ ≠ 0`, `n ≥ 2`, `r > 0`).
    • `rebased_no_offOrigin_kill` — ★ structural NON-COLLAPSE: at fat `K` there is a NONZERO source
      `q ∈ K` at which the gate leaves the kernel fully alive (`gatedKernel = if p ∈ S q then H
      else 0`) — the J4-602 collapse mechanism (`singleton_gatedKernel_offOrigin_zero`, which fed
      `leviSeries = −E`) is STRUCTURALLY UNAVAILABLE at fat `K`; with
      `rebased_hBdom_noncollapse` (positive source measure + nonzero source point) no
      a.e.-source-kill applies: the re-based `hBdom` is a bound on a GENUINE Neumann/Volterra
      series, not on `−E`.  (Whether individual iterates vanish for ANALYTIC reasons is not — and
      cannot honestly be — excluded here; what is excluded is the {0}-pin's structural kill.)
    • `gated_hBdom_of_defect_bound` — ★★ THE GENERAL-`K` ENGINE ASSEMBLY: the entire J4-597 route
      (`hEzero` = `heatOp_gatedWitnessN1_eq_zero_of_nonpos` → `hInt` =
      `iterConvIntegrableW_of_locally_bound_baseMeas` → D2 engine `leviSeries_dominatedW_le` →
      `baseKernelW_zero_apply`) factored GENERIC in `(g, gi, K, S)` — J4-597 had inlined it at
      `{0}`.  Width bookkeeping unchanged: the iterated majorants stay at width EXACTLY 2
      (`iterKernelW_eq`; `k`-growth absorbed into factorially-decaying `modelCoeff` scalars), the
      bound is CLEAN (no cap), conclusion at the literal `hBdom` width `gaussDdim (2s)`.
    • `gated_hBdom_engine_inhabited_at_center` — ★ antecedent-INHABITANCE certificate for the
      engine: at the banked `{0}` pkg (`curvedRNC_heatOp_dom_pkg`) the engine's `hbound` antecedent
      bundle IS inhabited at the genuinely-curved witness — so the factored engine lemma is not
      vacuous-by-shape.  ⚠ honesty: the inhabitance is at the DEGENERATE base `{0}` (where J4-602
      proved the series collapses); it certifies the LEMMA's non-vacuity, NOT fat-`K` satisfiability.
    • `rebased_hBdom_of_defect_bound` — ★★ THE RE-BASED `hBdom`: the engine instantiated at
      `K := closedBall 0 r`, `S := constGate … c`, curved witness — the EXACT `hBdom` binder shape
      of the general-`K` J4-596 builder, conditional on {`hEmeas` fat-`K` (M1), (hbound-fat)}.
    • `rebased_hInnerCont_of_dominations` — ★★ the CONSUMPTION certificate: the re-based `hBdom`
      genuinely fills the general-`K` builder `CurvedA1HContDom.curved_hInnerCont_of_dominations`
      at `K = closedBall 0 r`: given (hbound-fat) + `hEmeas` + the three remaining fat-`K` carries
      `{hAdom, hmeas, hcont}`, the capstone's `hInnerCont` `ContinuousOn` conclusion HOLDS at the
      fat base compact.
    • `rebased_hBdom_noncollapse`, `rebased_hBdom_curved_satisfiable` — non-vacuity gates.

  ── HONEST RESIDUAL.  OPEN: the (hbound-fat) PRODUCER (center-only-gauge amplitude rework — the
  wall), fat-`K` `hEmeas` (M1), fat-`K` `hAdom`/`hmeas` (re-based `hmeas` partially landed in
  J4-602)/`hcont`, the co-instantiated capstone application, the census/domination piles, the
  convergence trio, `hmassone`'s pre-ρ carriers, and the `hjets` residual.  `a₁ = R/6` is
  established non-vacuously ONLY for the FLAT tower; the curved case remains CONDITIONAL.

  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous antecedent posing as discharge
  (every conditional is labelled), no existing file edited except the `QIQTH.lean`/`AxiomAudit.lean`
  wiring, nothing committed.
-/
import Mathlib
import QIQTH.CurvedRNCHeatOpDomPkg
import QIQTH.GatedWitnessPackage
import QIQTH.CurvedA1HContDom
import QIQTH.CurvedA1ReBase
import QIQTH.CurvedA1FintHFarCoercivity

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.TrueHeatKernel QIQTH.LeviSeries
open QIQTH.A1R6CoreAtGate QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.GaussGaugeToHgauge QIQTH.GaussianWidthTolerant
open QIQTH.CurvedRNCHeatOpDomPkg QIQTH.CurvedA1FintHFarCoercivity
open scoped Topology

namespace QIQTH.CurvedA1ReBaseHBdom

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### STEP 1 outputs — the proved K-genericity verdict and the structural non-collapse. -/

/-- **A0 — a genuinely-nonzero point of the fat base compact.**  The axis point `(r/2)·e₀` lies in
    `closedBall 0 r` (`r > 0`, sup-norm) and is nonzero.  It witnesses `closedBall 0 r ≠ {0}` at
    EVERY radius `r > 0` (scales the J4-584 unit-ball point).  NOT `a₁ = R/6`. -/
theorem rebased_axis_point (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) :
    (Pi.single (⟨0, hn⟩ : Fin n) (r / 2 : ℝ)) ∈ Metric.closedBall (0 : Point n) r
      ∧ (Pi.single (⟨0, hn⟩ : Fin n) (r / 2 : ℝ)) ≠ (0 : Point n) := by
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hr.le]
    intro i
    rcases eq_or_ne i (⟨0, hn⟩ : Fin n) with h | h
    · subst h
      rw [Pi.single_eq_same, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · rw [Pi.single_eq_of_ne h, norm_zero]
      exact hr.le
  · intro hzero
    have hc := congrFun hzero (⟨0, hn⟩ : Fin n)
    rw [Pi.single_eq_same, Pi.zero_apply] at hc
    linarith

/-- **★★ J4-603 (VERDICT) — `rebased_hframeK_unsat`: the CONST defect-bound producer chain does NOT
    re-instantiate at the fat base compact.**  The whole banked producer chain
    (`gatedWitnessN1_hEboundW_le_lin_CONST` and everything below it) carries
    `hframeK : ∀ q ∈ K, g q = δ` — K-parametric in FORM but δ-frame-demanding at EVERY base point.
    At the genuinely-curved witness (`κ ≠ 0`, `n ≥ 2`) and `K = closedBall 0 r` (`r > 0`) this
    antecedent PROVABLY FAILS: the fat-`K` `hBdom` CANNOT be produced by mere re-instantiation of
    the J4-597 route, and any such "instantiation" would be vacuous (cp466 blind spot).  The missing
    estimate is scoped in the header ((hbound-fat): center-only-gauge amplitude rework).  NOT
    `a₁ = R/6`. -/
theorem rebased_hframeK_unsat (κ r : ℝ) (hκ : κ ≠ 0) (hn : 2 ≤ n) (hr : 0 < r) :
    ¬ (∀ q ∈ Metric.closedBall (0 : Point n) r, ∀ i j,
        curvedRNCMetric κ q i j = (if i = j then (1 : ℝ) else 0)) := by
  intro hframe
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  obtain ⟨hqmem, hqne⟩ := rebased_axis_point (n := n) hn1 r hr
  exact hqne (curvedRNCMetric_frame_forces_origin κ hκ hn (hframe _ hqmem))

open Classical in
/-- **★ J4-603 — `rebased_no_offOrigin_kill`: the structural NON-COLLAPSE of the fat-`K` series.**
    At `K = closedBall 0 r` (`r > 0`) there is a NONZERO source `q ∈ K` at which the gated kernel is
    fully alive (`gatedKernel K S H τ p q = if p ∈ S q then H τ p q else 0`, for EVERY gate `S`,
    kernel `H`, time `τ`, target `p`).  The J4-602 collapse chain
    (`singleton_gatedKernel_offOrigin_zero` → `E` off-origin-dead → `leviSeries = −E`) is therefore
    STRUCTURALLY UNAVAILABLE at the fat base: the re-based `hBdom` bounds a GENUINE Neumann/Volterra
    series.  (Analytic vanishing of individual iterates is not excluded — only the {0}-pin's
    structural source-kill is.)  NOT `a₁ = R/6`. -/
theorem rebased_no_offOrigin_kill (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) :
    ∃ q : Point n, q ∈ Metric.closedBall (0 : Point n) r ∧ q ≠ 0 ∧
      ∀ (S : Point n → Set (Point n)) (H : ℝ → Point n → Point n → ℝ) (τ : ℝ) (p : Point n),
        gatedKernel (Metric.closedBall (0 : Point n) r) S H τ p q
          = if p ∈ S q then H τ p q else 0 := by
  obtain ⟨hqmem, hqne⟩ := rebased_axis_point (n := n) hn r hr
  exact ⟨_, hqmem, hqne, fun S H τ p =>
    QIQTH.CurvedA1ReBase.rebased_gate_source_open r S H τ p hqmem⟩

/-! ### STEP 2 — the general-`K` engine assembly and its fat-`K` instantiation. -/

/-- **★★ J4-603 — `gated_hBdom_of_defect_bound`: THE GENERAL-`K` WIDTH-2 LEVI-SERIES ENGINE
    ASSEMBLY.**  The complete J4-597 Neumann-tail route, factored GENERIC in the metric bundle
    `(g, gi, hChr)`, the base compact `K`, and the gate `S` (J4-597 had inlined it at `K = {0}`):
    GIVEN the joint strong measurability `hEmeas` of the defect kernel (M1) and the all-`t'` width-2
    defect bound `hbound`, the signed Levi series is Gaussian-dominated on `(0,T]`:
        `|leviSeries (heatOp g gi W) s z y| ≤ C_L · gaussDdim (2s) (z − y)`.
    Route: `hEzero` (`heatOp_gatedWitnessN1_eq_zero_of_nonpos`, generic in `K`/`S`, needs `1 ≤ n`)
    → `hInt` (`iterConvIntegrableW_of_locally_bound_baseMeas`) → the D2 engine
    (`leviSeries_dominatedW_le`; iterated majorants stay at width EXACTLY 2, `k`-growth absorbed
    into the factorially-decaying `modelCoeff`) → `baseKernelW_zero_apply`.  CLEAN bound (no cap),
    clean width 2 (no widening).  NOT `a₁ = R/6`. -/
theorem gated_hBdom_of_defect_bound (g gi : Point n → Fin n → Fin n → ℝ) (hn : 1 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (a b C T : ℝ) (hC0 : 0 ≤ C) (hT : 0 < T)
    (hEmeas : StronglyMeasurable (fun w : ℝ × Point n × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) w.1 w.2.1 w.2.2))
    (hbound : ∀ (t' τ : ℝ) (p q : Point n), 0 < τ → τ ≤ t' →
        |heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q|
          ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q) :
    ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
      |leviSeries (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) s z y|
        ≤ C_L * gaussDdim (2 * s) (z - y) := by
  classical
  -- `hEzero`: the defect kernel vanishes at nonpositive time (generic in `K` and `S`).
  have hEzero : ∀ τ : ℝ, τ ≤ 0 → ∀ p q : Point n,
      heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) τ p q = 0 :=
    heatOp_gatedWitnessN1_eq_zero_of_nonpos g gi hn K S
      (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) a b
      (uniformInverseChart g gi hChr hK)
  -- `hInt`: the per-step integrability family from `hEzero` + `hEmeas` + the local bound family.
  have hInt : IterConvIntegrableW
      (heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b)) (2 : ℝ) (0 : ℝ) (C * (1 + T)) :=
    iterConvIntegrableW_of_locally_bound_baseMeas _ (C * (1 + T)) hEzero hEmeas
      (fun T' hT' => ⟨C * (1 + T'), mul_nonneg hC0 (by linarith),
        fun τ p q hτ hτT' => hbound T' τ p q hτ hτT'⟩)
  -- the D2 engine: the width-2 Levi-series domination on `(0,T]`.
  obtain ⟨C_L, hCL0, hdom⟩ :=
    leviSeries_dominatedW_le _ (C * (1 + T)) T (mul_nonneg hC0 (by linarith)) hT
      (fun τ p q hτ hτT => hbound T τ p q hτ hτT) hInt
  refine ⟨C_L, hCL0, fun s hs hsT z y => ?_⟩
  have h := hdom s z y hs hsT
  rwa [baseKernelW_zero_apply] at h

/-- **★ J4-603 — `gated_hBdom_engine_inhabited_at_center`: the engine antecedent is INHABITED.**
    The `hbound` antecedent bundle of `gated_hBdom_of_defect_bound` is genuinely satisfiable at the
    curved witness — by the banked `curvedRNC_heatOp_dom_pkg` at the base `K = {0}` (∃ gate
    parameters `0 < a < b < c`, `C ≥ 0` with the exact all-`t'` width-2 bound).  So the factored
    engine lemma is NOT vacuous-by-shape.  ⚠ HONESTY: this inhabitance is at the DEGENERATE base
    `{0}` where J4-602 proved the series collapses to `−E`; it certifies the LEMMA's antecedent
    inhabitance, NOT satisfiability of the fat-`K` instantiation's antecedent — the latter is the
    scoped OPEN wall ((hbound-fat)).  NOT `a₁ = R/6`. -/
theorem gated_hBdom_engine_inhabited_at_center (κ : ℝ) (hκ : κ < 0)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (foldedCoeff (vanVleck (curvedRNCMetric κ))
        (transportCoeff (transportOp (vanVleck (curvedRNCMetric κ))
          (curvedRNCMetric κ) (curvedRNCInv κ))) k : Point n → ℝ))
    (T : ℝ) :
    ∃ a b C c : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ b < c ∧
      ∀ (t' τ : ℝ) (p q : Point n), 0 < τ → τ ≤ t' →
        |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
            (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n))))
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                ((isCompact_singleton : IsCompact ({(0 : Point n)} : Set (Point n)))) c) a b)
            τ p q|
          ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q := by
  obtain ⟨a, b, C, c, ha, hab, hC0, hbc, hpkg, -⟩ :=
    curvedRNC_heatOp_dom_pkg κ hκ hChr hw T
  exact ⟨a, b, C, c, ha, hab, hC0, hbc, hpkg⟩

/-- **★★ J4-603 — `rebased_hBdom_of_defect_bound`: THE RE-BASED `hBdom` AT THE FAT BASE COMPACT.**
    The width-2 Levi-series Gaussian domination for the genuinely-curved witness
    `g^K = curvedRNCMetric κ` at `K := Metric.closedBall 0 r` on the constant-radius flow-ball gate
    `constGate … c` — the EXACT `hBdom` binder shape of the general-`K` J4-596 builder
    (`CurvedA1HContDom.curved_hInnerCont_of_dominations` at `hK := isCompact_closedBall 0 r`),
    conditional on exactly TWO labelled inputs:
      • `hEmeas` — the fat-`K` M1 joint strong measurability of the defect kernel;
      • `hbound` — (hbound-fat), THE precisely-scoped missing estimate: the all-`t'` width-2 defect
        bound at the fat base compact.  Its producer is the OPEN wall — the banked CONST chain
        CANNOT supply it (`rebased_hframeK_unsat`); a center-only-gauge amplitude rework is needed.
    By `rebased_no_offOrigin_kill` + `rebased_hBdom_noncollapse` the dominated series at THIS `K` is
    NOT structurally collapsed to `−E` — the Neumann-tail machinery (`hInt`, the D2 engine, the
    width-2 iterated majorants) is exercised for real.  Gate parameters `a b c` and the radius `r`
    are universally quantified here (they belong to the assumed bound); the joint `(a,b,c,r)`
    prescribed-ceiling production is the future producer's obligation.  NOT `a₁ = R/6`. -/
theorem rebased_hBdom_of_defect_bound (κ r : ℝ) (hn : 1 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (a b c C T : ℝ) (hC0 : 0 ≤ C) (hT : 0 < T)
    (hEmeas : StronglyMeasurable (fun w : ℝ × Point n × Point n =>
        heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            (isCompact_closedBall (0 : Point n) r)
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              (isCompact_closedBall (0 : Point n) r) c) a b) w.1 w.2.1 w.2.2))
    (hbound : ∀ (t' τ : ℝ) (p q : Point n), 0 < τ → τ ≤ t' →
        |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
            (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              (isCompact_closedBall (0 : Point n) r)
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                (isCompact_closedBall (0 : Point n) r) c) a b) τ p q|
          ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q) :
    ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ s, 0 < s → s ≤ T → ∀ z y : Point n,
      |leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            (isCompact_closedBall (0 : Point n) r)
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              (isCompact_closedBall (0 : Point n) r) c) a b)) s z y|
        ≤ C_L * gaussDdim (2 * s) (z - y) :=
  gated_hBdom_of_defect_bound (curvedRNCMetric κ) (curvedRNCInv κ) hn hChr
    (isCompact_closedBall (0 : Point n) r)
    (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
      (isCompact_closedBall (0 : Point n) r) c) a b C T hC0 hT hEmeas hbound

/-- **★★ J4-603 — `rebased_hInnerCont_of_dominations`: THE FAT-`K` CONSUMPTION CERTIFICATE.**  The
    re-based `hBdom` genuinely fills the `hBdom` slot of the GENERAL-`K` J4-596 builder at
    `K = closedBall 0 r`: given (hbound-fat) + the M1 carry `hEmeas` + the three remaining fat-`K`
    carries `{hAdom, hmeas, hcont}` at the same gate parameters, the capstone's carried `hInnerCont`
    conclusion — interior-time `ContinuousOn` of the inner space-time pairing on `Ioo 0 u` — HOLDS
    for `g^K` at the FAT base compact, via
    `CurvedA1HContDom.curved_hInnerCont_of_dominations` (general-`K`) with the `hBdom` slot supplied
    by `rebased_hBdom_of_defect_bound`.  This is the first fat-`K` exercise of the whole width-2
    assembly.  NOT `a₁ = R/6`. -/
theorem rebased_hInnerCont_of_dominations (κ r : ℝ) (hn : 1 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    (a b c C T : ℝ) (hC0 : 0 ≤ C) (hT : 0 < T) (U : Set ℝ) (hUT : ∀ u ∈ U, u ≤ T)
    (hEmeas : StronglyMeasurable (fun w : ℝ × Point n × Point n =>
        heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
          (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            (isCompact_closedBall (0 : Point n) r)
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              (isCompact_closedBall (0 : Point n) r) c) a b) w.1 w.2.1 w.2.2))
    (hbound : ∀ (t' τ : ℝ) (p q : Point n), 0 < τ → τ ≤ t' →
        |heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
            (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              (isCompact_closedBall (0 : Point n) r)
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                (isCompact_closedBall (0 : Point n) r) c) a b) τ p q|
          ≤ (C * (1 + t')) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (A₀ A₁ : ℝ) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hAdom : ∀ τ, 0 < τ → ∀ p q : Point n,
        |vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            (isCompact_closedBall (0 : Point n) r)
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              (isCompact_closedBall (0 : Point n) r) c) a b τ p q|
          ≤ (A₀ + A₁ * τ) * Real.sqrt (3 / 2) ^ n * gaussDdim (3 / 2 * τ) (p - q))
    (hmeas : ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᶠ s in 𝓝 s₀,
        AEStronglyMeasurable
          (fun z => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              (isCompact_closedBall (0 : Point n) r)
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                (isCompact_closedBall (0 : Point n) r) c) a b (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                  (isCompact_closedBall (0 : Point n) r)
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                    (isCompact_closedBall (0 : Point n) r) c) a b)) s z 0)
          (volume : Measure (Point n)))
    (hcont : ∀ u ∈ U, ∀ s₀ ∈ Set.Ioo (0 : ℝ) u, ∀ᵐ z ∂(volume : Measure (Point n)),
        ContinuousAt
          (fun s => vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              (isCompact_closedBall (0 : Point n) r)
              (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                (isCompact_closedBall (0 : Point n) r) c) a b (u - s) 0 z
            * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
                (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                  (isCompact_closedBall (0 : Point n) r)
                  (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                    (isCompact_closedBall (0 : Point n) r) c) a b)) s z 0) s₀) :
    ∀ u ∈ U, ContinuousOn
        (fun s => ∫ z, vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
            (isCompact_closedBall (0 : Point n) r)
            (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
              (isCompact_closedBall (0 : Point n) r) c) a b (u - s) 0 z
          * leviSeries (heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
              (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                (isCompact_closedBall (0 : Point n) r)
                (constGate (curvedRNCMetric κ) (curvedRNCInv κ) hChr
                  (isCompact_closedBall (0 : Point n) r) c) a b)) s z 0)
        (Set.Ioo 0 u) := by
  obtain ⟨C_L, hCL0, hBdom⟩ :=
    rebased_hBdom_of_defect_bound κ r hn hChr a b c C T hC0 hT hEmeas hbound
  exact QIQTH.CurvedA1HContDom.curved_hInnerCont_of_dominations κ hChr
    (isCompact_closedBall (0 : Point n) r) a b c T U hUT
    A₀ A₁ C_L hA₀ hA₁ hCL0 hAdom hBdom hmeas hcont

/-! ### Non-vacuity gates. -/

/-- **★ J4-603 — `rebased_hBdom_noncollapse`: the co-instantiation non-collapse bundle.**  The fat
    base compact has POSITIVE Lebesgue measure AND contains a nonzero point — the two facts that
    jointly rule out both J4-602 collapse mechanisms (a.e.-source-kill via null support; off-origin
    gate-kill).  NOT `a₁ = R/6`. -/
theorem rebased_hBdom_noncollapse (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) :
    0 < (volume : Measure (Point n)) (Metric.closedBall (0 : Point n) r)
      ∧ ∃ q : Point n, q ∈ Metric.closedBall (0 : Point n) r ∧ q ≠ 0 :=
  ⟨QIQTH.CurvedA1ReBase.rebased_base_pos_measure hn r hr,
   ⟨_, (rebased_axis_point hn r hr).1, (rebased_axis_point hn r hr).2⟩⟩

/-- **★ J4-603 — the usual curvature gate**: the re-based witness metric is GENUINELY curved for
    `κ < 0`, `n ≥ 2` (`∃ w, 1 < det g^K w`).  Re-exports the banked certificate.  NOT `a₁ = R/6`. -/
theorem rebased_hBdom_curved_satisfiable (κ : ℝ) (hκ : κ < 0) (hn : 2 ≤ n) :
    ∃ w : Point n, (1 : ℝ) < Matrix.det (curvedRNCMetric κ w) :=
  QIQTH.CurvedA1ReBase.rebased_satisfiable κ hκ hn

end QIQTH.CurvedA1ReBaseHBdom

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks

open QIQTH.CurvedA1ReBaseHBdom

#print axioms rebased_axis_point
#print axioms rebased_hframeK_unsat
#print axioms rebased_no_offOrigin_kill
#print axioms gated_hBdom_of_defect_bound
#print axioms gated_hBdom_engine_inhabited_at_center
#print axioms rebased_hBdom_of_defect_bound
#print axioms rebased_hInnerCont_of_dominations
#print axioms rebased_hBdom_noncollapse
#print axioms rebased_hBdom_curved_satisfiable

end AxiomChecks
