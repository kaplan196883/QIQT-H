/-
  ConstRadiusGateExport — J4-316: re-exporting the residual provider's gate package with the flow-ball
  radius exposed as the CONSTANT it secretly is, and thereby DISSOLVING the single named S1 residue
  `Measurable cf`.  ONE brick of the `a₁ = R/6` heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It performs a
  purely bookkeeping re-export: the gate `S` that the residual provider chooses is, secretly, a flow-ball
  of a SINGLE CONSTANT radius `c = (b+ρc)/2`; the landed package hid that constant behind a per-point
  `Classical.choose`, so its exported radius `cf` was opaque (neither measurable nor constant survived).
  Here we replay the SAME package-merge with the constant substituted for the `.choose`, exposing `c`.
  No `sorry` (prose excepted), no new axioms, no `:= True`, no vacuous / unsatisfiable hypotheses, no
  conclusion-in-disguise.  No existing file is edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (U0) RECON — the package ∃-shape, the field-transfer verdicts, the radius bookkeeping.

  ── THE PACKAGE ∃-SHAPE (from `GateOpennessExport.gatedWitnessN1_package_open`, A3′):
        `∃ a b C : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ ∃ S : Point n → Set (Point n),
           (∀ t, ∀ τ p q, 0<τ→τ≤t → |heatOp g gi (gatedKernel K S H) τ p q| ≤ (C·(1+t))·baseKernelW 2 0 τ p q)
           ∧ (0 ∈ K → 0 ∈ S 0) ∧ (0 ∈ K → IsOpen (S 0))`
     with `H = globalCutoffParametrixWitnessN 1 (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi))
     a b (uniformInverseChart g gi hC hK)` and the exported gate
        `S = fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 (cf q)`,  `cf q = (hgood q hq).choose`.

  ── THE `_of_good` FIELD LIST (the 7-conjunct `hgood` body, per `q ∈ K`, for the exported gate at radius
     `c`, read off `.choose_spec`):
        (1) `∀ τ>0, ∀ ‖v‖<c, |heatOp H τ (φ_q v) q| ≤ (B₀+B₁τ)·gaussDdim (2τ) (φ_q v - q)`  — mixed bound,
        (2) `∀ ‖v‖≤c, W q (φ_q v) = v`                                                      — germ left-inverse,
        (3) `∀ ‖v‖≤c, ContinuousAt (W q) (φ_q v)`                                            — continuity,
        (4) `IsOpen (φ_q '' ball 0 c)`                                                        — gate openness,
        (5) `closure (φ_q '' ball 0 c) ⊆ φ_q '' closedBall 0 c`                               — frontier collar,
        (6) `∀ ‖v‖<c, rncRadialSq (φ_q v - q) ≤ (3/2)·rncRadialSq v`                          — square control,
        (7) `q ∈ φ_q '' ball 0 c`                                                             — base membership.
     `_of_good_pkg_open` assembles from these a 3-leg MIXED cover (in-gate leg via (1),(4); off-gate leg via
     (5); frontier-collar leg via (2),(3) + cutoff vanishing) and reads the package fields off (4),(6),(7).

  ── FIELD-TRANSFER VERDICT (constant radius).  In `_lin_pkg_open` every one of (1)–(7) is DISCHARGED
     UNIFORMLY at the SINGLE constant `c = (b+ρc)/2` — the per-`q` proof body `refine ⟨c, hbc, …⟩` uses only
     the germ/chart facts `hchartGerm q hq`, `hchartOC q hq`, `hdisp q hq`, `hAbound τ hτ q hq`, which are
     q-parametric but produce (1)–(7) at the FIXED `c`.  So `_of_good_pkg_open`'s ONLY use of the `.choose`
     was to name a per-`q` radius that was, in fact, always this constant.  Hence EVERY field transfers
     VERBATIM to the constant gate `fun q => φ_q '' ball 0 c`: the mixed-cover proof is copied with the
     `dif`/`.choose` indirection dropped (`cf q ↦ c`, `.choose_spec ↦ hgoodC q hq`).  No field genuinely
     needed the `.choose` (there is no per-`q` optimality — `c` is chosen once, before `q`).

  ── RADIUS BOOKKEEPING.  The exposed constant is `c = (b+ρc)/2` with `b < c < ρc = min (min rN δ₀) r₁`, so
     `b < c` and `c < δ₀` (the CHART reach of `uniformInverseChart_huniformChart`).  The S1 discharge
     `S1TripleHEmeasGate.tripleHEmeas_flowball_geometry` supplies its OWN reach `δ₀' > 0` (from the JET
     machinery `tripleHEmeas_Gc_concrete`) and needs `b < c < δ₀'`.  These two reaches are a-priori
     DIFFERENT; the honest compatibility condition `c < δ₀'` is therefore carried as the ANTECEDENT of the
     S1 conclusion (`∃ δ₀ > 0, c < δ₀ → tripleHEmeas …`) — a satisfiable smallness condition, never assumed.
     The J4-315 reach bound `∀ q ∈ K, cf q < δ₀` becomes, for the constant `cf = fun _ => c`, exactly
     `c < δ₀`, and its S1 residue `Measurable cf` becomes `Measurable (fun _ => c) = measurable_const` —
     DISSOLVED.

  ## (U1) `gatedWitnessN1_package_open_CONSTRADIUS` — BANKED.  The A3′ package with the constant radius `c`
  EXPOSED and the gate written literally as `fun z => φ_z '' ball 0 c` (no `.choose`).  Built by replaying
  `_of_good_pkg_open` (→ `gatedWitnessN1_hEboundW_le_of_good_CONST`) and `_lin_pkg_open`
  (→ `gatedWitnessN1_hEboundW_le_lin_CONST`) with the constant substituted.

  ## (U2) `tripleHEmeas_AT_CONSTRADIUS_GATE` — BANKED.  S1 at the constant gate, from geometry alone, via
  `tripleHEmeas_flowball_geometry` specialized to the exposed `c` — the `Measurable cf` residue dissolved.

  ## (U3) `constRadius_package_and_S1` — BANKED.  The two ingredients bundled for the future v3-export.

  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.GateOpennessExport
import QIQTH.S1TripleHEmeasGate

open MeasureTheory Finset Filter
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.FlatHeatEquation
open QIQTH.HeatParametrixAnsatz QIQTH.HeatParametrixOrder
open QIQTH.GaussianPolyBound QIQTH.ResidueBound QIQTH.RNCDecay
open QIQTH.PullbackMetric QIQTH.ExpMap QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction QIQTH.LeviSeries
open QIQTH.HeatDuhamel QIQTH.HeatResidualBound
open QIQTH.GateOpennessExport QIQTH.S1TripleHEmeasGate
open scoped BigOperators ContDiff Topology Interval

namespace QIQTH.ConstRadiusGateExport

variable {n : ℕ}

set_option maxHeartbeats 2400000

/-! ### (U1a) — `_of_good_CONST`: the `_of_good_pkg_open` merge at a CONSTANT radius `c`. -/

/-- **★ J4-316 (U1a) — the CONSTANT-RADIUS `_of_good`.**  Verbatim
    `GateOpennessExport.gatedWitnessN1_hEboundW_le_of_good_pkg_open`, with the per-`q` covering `.choose`
    radius replaced by a SINGLE constant `c` (the `hgood` existential is discharged uniformly at `c`, so
    the `dif`/`.choose` indirection is dropped and the gate is the literal `fun q => φ_q '' ball 0 c`).
    Every field of the merge transfers verbatim — see the header (U0) field-transfer verdict.  NOT
    `a₁ = R/6`. -/
theorem gatedWitnessN1_hEboundW_le_of_good_CONST (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (a b B₀ B₁ : ℝ) (ha : 0 < a) (hab : a < b) (hB0 : 0 ≤ B₀) (hB1 : 0 ≤ B₁)
    (W : Point n → Point n → Point n)
    (c : ℝ) (hbc : b < c)
    (hgoodC : ∀ q ∈ K,
      (∀ τ, 0 < τ → ∀ v : Point n, ‖v‖ < c →
        |heatOp g gi (globalCutoffParametrixWitnessN 1 Θ u a b (W)) τ
            (uniformFlowExp g gi hC hK q v) q|
          ≤ (B₀ + B₁ * τ) * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q)) ∧
      (∀ v : Point n, ‖v‖ ≤ c →
        W q (uniformFlowExp g gi hC hK q v) = v) ∧
      (∀ v : Point n, ‖v‖ ≤ c →
        ContinuousAt (W q) (uniformFlowExp g gi hC hK q v)) ∧
      IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball 0 c) ∧
      closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c)
        ⊆ uniformFlowExp g gi hC hK q '' Metric.closedBall 0 c ∧
      (∀ v : Point n, ‖v‖ < c →
        rncRadialSq (uniformFlowExp g gi hC hK q v - q) ≤ (3 / 2 : ℝ) * rncRadialSq v) ∧
      q ∈ uniformFlowExp g gi hC hK q '' Metric.ball 0 c) :
    (∀ (t : ℝ), ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (gatedKernel K (fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 c)
            (globalCutoffParametrixWitnessN 1 Θ u a b (W))) τ p q|
          ≤ (max B₀ B₁ * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
      ∧ GateSqControl K (fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 c) W
      ∧ (∀ q ∈ K, q ∈ (fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 c) q)
      ∧ (∀ q ∈ K, IsOpen ((fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 c) q)) := by
  classical
  set H : ℝ → Point n → Point n → ℝ :=
    globalCutoffParametrixWitnessN 1 Θ u a b (W) with hHdef
  have hCmax0 : (0 : ℝ) ≤ max B₀ B₁ := le_trans hB0 (le_max_left _ _)
  have hb0 : 0 < b := lt_trans ha hab
  -- the 3-leg MIXED cover for the CONSTANT-radius gate `S q := φ_q '' (ball 0 c)`.
  have hcover : ∀ q, q ∈ K → ∀ τ, 0 < τ → ∀ p,
      ((fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 c) q ∈ nhds p
          ∧ |heatOp g gi H τ p q|
            ≤ max B₀ B₁ * (baseKernelW (2 : ℝ) (0 : ℝ) τ p q + baseKernelW (2 : ℝ) (1 : ℝ) τ p q))
      ∨ ({p' : Point n | p' ∉ (fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 c) q}
          ∈ nhds p)
      ∨ ((fun s => H s p q) =ᶠ[nhds τ] (fun _ => (0 : ℝ))
          ∧ (fun p' => H τ p' q) =ᶠ[nhds p] (fun _ => (0 : ℝ))) := by
    intro q hq τ hτ p
    obtain ⟨hbnd, hinv, hcont, hopen, hclos, _, _⟩ := hgoodC q hq
    by_cases hpS : p ∈ uniformFlowExp g gi hC hK q '' Metric.ball 0 c
    · -- LEG 1 (in-gate): transfer the mixed in-chart bound, converting to the MIXED `baseKernelW` shape.
      refine Or.inl ⟨hopen.mem_nhds hpS, ?_⟩
      obtain ⟨w, hw, hwp⟩ := hpS
      rw [mem_ball_zero_iff] at hw
      have hb := hbnd τ hτ w hw
      rw [hwp] at hb
      rw [baseKernelW_one_eq_tau_mul, baseKernelW_zero_apply]
      have hG : (0 : ℝ) ≤ gaussDdim (2 * τ) (p - q) := gaussDdim_nonneg _ _
      have hle : B₀ + B₁ * τ ≤ max B₀ B₁ * (1 + τ) := by
        have h2 : B₁ ≤ max B₀ B₁ := le_max_right _ _
        nlinarith [mul_le_mul_of_nonneg_right h2 hτ.le, le_max_left B₀ B₁]
      calc |heatOp g gi H τ p q|
          ≤ (B₀ + B₁ * τ) * gaussDdim (2 * τ) (p - q) := hb
        _ ≤ (max B₀ B₁ * (1 + τ)) * gaussDdim (2 * τ) (p - q) :=
            mul_le_mul_of_nonneg_right hle hG
        _ = max B₀ B₁ * (gaussDdim (2 * τ) (p - q) + τ * gaussDdim (2 * τ) (p - q)) := by ring
    · by_cases hpcl : p ∈ closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c)
      · -- LEG 3 (frontier collar): the cutoff of `W_q` vanishes near `p`, zeroing the whole witness.
        obtain ⟨w', hw', hw'p⟩ := hclos hpcl
        rw [mem_closedBall_zero_iff] at hw'
        have hnormeq : ‖w'‖ = c := by
          rcases lt_or_eq_of_le hw' with hlt | heq
          · exact absurd (⟨w', mem_ball_zero_iff.mpr hlt, hw'p⟩ :
              p ∈ uniformFlowExp g gi hC hK q '' Metric.ball 0 c) hpS
          · exact heq
        have hWp : W q p = w' := by
          rw [← hw'p]; exact hinv w' hw'
        have hb2 : b ^ 2 < rncRadialSq (W q p) := by
          rw [hWp]
          have h1 : ‖w'‖ ^ 2 ≤ rncRadialSq w' := by
            have hle := norm_le_rncRadial w'
            have := rncRadial_sq w'
            nlinarith [norm_nonneg w', rncRadial_nonneg w', hle, this]
          nlinarith [h1, hnormeq, hb0, hbc]
        have hcontp : ContinuousAt (W q) p := by
          rw [← hw'p]; exact hcont w' hw'
        have hNnhds :
            (W q) ⁻¹' {w : Point n | b ^ 2 < rncRadialSq w} ∈ nhds p :=
          hcontp.preimage_mem_nhds ((isOpen_rncRadialSq_gt (b ^ 2)).mem_nhds hb2)
        refine Or.inr (Or.inr ⟨?_, ?_⟩)
        · refine Filter.Eventually.of_forall (fun s => ?_)
          simp only [hHdef, globalCutoffParametrixWitnessN]
          rw [radialCutoff_eq_zero ha hab (le_of_lt hb2), zero_mul]
        · filter_upwards [hNnhds] with p' hp'
          have hp'2 : b ^ 2 < rncRadialSq (W q p') := hp'
          simp only [hHdef, globalCutoffParametrixWitnessN]
          rw [radialCutoff_eq_zero ha hab (le_of_lt hp'2), zero_mul]
      · -- LEG 2 (off-gate): the complement of the closed closure is a neighborhood.
        refine Or.inr (Or.inl ?_)
        have hsub : (closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c))ᶜ
            ⊆ {p' : Point n | p' ∉ uniformFlowExp g gi hC hK q '' Metric.ball 0 c} :=
          fun x hx hxS => hx (subset_closure hxS)
        exact Filter.mem_of_superset (isClosed_closure.isOpen_compl.mem_nhds hpcl) hsub
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    exact gatedKernel_hEboundW_le_of_mixedCover g gi K
      (fun q => uniformFlowExp g gi hC hK q '' Metric.ball 0 c) H (max B₀ B₁) t hCmax0 hcover
  · -- `GateSqControl` for the constant-radius gate, from field (6).
    intro q hq p hp
    obtain ⟨_, hinv, _, _, _, hsqc, _⟩ := hgoodC q hq
    obtain ⟨v, hvmem, hvp⟩ := hp
    rw [mem_ball_zero_iff] at hvmem
    have hWp : W q p = v := by rw [← hvp]; exact hinv v (le_of_lt hvmem)
    calc rncRadialSq (p - q)
        = rncRadialSq (uniformFlowExp g gi hC hK q v - q) := by rw [hvp]
      _ ≤ (3 / 2 : ℝ) * rncRadialSq v := hsqc v hvmem
      _ = (3 / 2 : ℝ) * rncRadialSq (W q p) := by rw [hWp]
  · -- base-point membership `∀ q ∈ K, q ∈ S q`, field (7).
    intro q hq
    obtain ⟨_, _, _, _, _, _, hmem⟩ := hgoodC q hq
    exact hmem
  · -- gate-openness `∀ q ∈ K, IsOpen (S q)`, field (4).
    intro q hq
    obtain ⟨_, _, _, hopen, _, _, _⟩ := hgoodC q hq
    exact hopen

/-! ### (U1b) — `_lin_CONST`: discharges the fields uniformly at `c = (b+ρc)/2`, exposing `c`. -/

/-- **★★ J4-316 (U1b) — the CONSTANT-RADIUS `_lin`.**  Verbatim
    `GateOpennessExport.gatedWitnessN1_hEboundW_le_lin_pkg_open`, but producing and EXPOSING the constant
    radius `c = (b+ρc)/2` (with `b < c`) and the literal constant gate `fun q => φ_q '' ball 0 c` — the
    per-`q` `hgood` discharge is lifted to a `q`-uniform `hgoodC` at the single `c`, which feeds
    `gatedWitnessN1_hEboundW_le_of_good_CONST`.  NOT `a₁ = R/6`. -/
theorem gatedWitnessN1_hEboundW_le_lin_CONST (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (hframeK : ∀ q ∈ K, ∀ i j, g q i j = (if i = j then (1 : ℝ) else 0))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hw : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞) (foldedCoeff Θ u k))
    (ρ_c C_c0 C_c1 : ℝ) (hρ_c : 0 < ρ_c) (hC_c0 : 0 ≤ C_c0) (hC_c1 : 0 ≤ C_c1)
    (hCoeffU0 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ u v| ≤ C_c0 * rncRadialSq v)
    (hCoeffLin1 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ_c →
      |totalRadialO1_coeff (uniformFlowPullbackMetric g gi hC hK q)
          (uniformFlowPullbackMetricInv g gi hC hK q) Θ (fun j => u (j + 1)) v|
        ≤ C_c1 * rncRadial v) :
    ∃ a b C c : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ b < c ∧
      (∀ (t : ℝ), ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi (gatedKernel K (fun z => uniformFlowExp g gi hC hK z '' Metric.ball 0 c)
            (globalCutoffParametrixWitnessN 1 Θ u a b (uniformInverseChart g gi hC hK))) τ p q|
          ≤ (C * (1 + t)) * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
      ∧ GateSqControl K (fun z => uniformFlowExp g gi hC hK z '' Metric.ball 0 c)
          (uniformInverseChart g gi hC hK)
      ∧ (∀ q ∈ K, q ∈ uniformFlowExp g gi hC hK q '' Metric.ball 0 c)
      ∧ (∀ q ∈ K, IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball 0 c)) := by
  obtain ⟨δ₀, hδ₀, hchart⟩ := uniformInverseChart_huniformChart g gi hC hK
  obtain ⟨rN, hrNpos, hnat⟩ :=
    laplaceBeltrami_uniformFlow_naturality_forall_f g gi hC hK hgsymm
  obtain ⟨r₁, hr₁pos, hdisp⟩ := uniformFlowExp_hdisp_ball g gi hC hK
  set W : Point n → Point n → Point n := uniformInverseChart g gi hC hK with hWdef
  set Sc : ℝ := Real.sqrt (2 / (3 / 2)) ^ n with hSc_def
  have hSc0 : 0 ≤ Sc := by positivity
  set ρc : ℝ := min (min rN δ₀) r₁ with hρcdef
  have hρc : 0 < ρc := lt_min (lt_min hrNpos hδ₀) hr₁pos
  have hρc_rN : ρc ≤ rN := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρc_δ₀ : ρc ≤ δ₀ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρc_r₁ : ρc ≤ r₁ := min_le_right _ _
  obtain ⟨a, b, B₀, B₁, ha, hab, hbρc, hB0, hB1, hAbound⟩ :=
    cutoffResidualN1_uniformFlow_narrow_mixed_below_lin g gi hg hC hK hgnd hgsymm hinvF hframeK Θ u hw
      ρ_c C_c0 C_c1 hρ_c hC_c0 hC_c1 hCoeffU0 hCoeffLin1 ρc hρc
  set B₀' : ℝ := B₀ * Sc with hB0'_def
  set B₁' : ℝ := B₁ * Sc with hB1'_def
  have hB0'0 : 0 ≤ B₀' := by rw [hB0'_def]; positivity
  have hB1'0 : 0 ≤ B₁' := by rw [hB1'_def]; positivity
  set c : ℝ := (b + ρc) / 2 with hcdef
  have hbc : b < c := by rw [hcdef]; linarith
  have hcρc : c < ρc := by rw [hcdef]; linarith
  have hc0 : 0 < c := lt_trans (lt_trans ha hab) hbc
  have hc_rN : c < rN := lt_of_lt_of_le hcρc hρc_rN
  have hc_δ₀ : c < δ₀ := lt_of_lt_of_le hcρc hρc_δ₀
  have hc_r₁ : c < r₁ := lt_of_lt_of_le hcρc hρc_r₁
  -- the 7-conjunct field bundle, discharged UNIFORMLY at the single constant `c` (per-`q` germ/chart data).
  have hgoodC : ∀ q ∈ K,
      (∀ τ, 0 < τ → ∀ v : Point n, ‖v‖ < c →
        |heatOp g gi (globalCutoffParametrixWitnessN 1 Θ u a b (W)) τ
            (uniformFlowExp g gi hC hK q v) q|
          ≤ (B₀' + B₁' * τ) * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q)) ∧
      (∀ v : Point n, ‖v‖ ≤ c →
        W q (uniformFlowExp g gi hC hK q v) = v) ∧
      (∀ v : Point n, ‖v‖ ≤ c →
        ContinuousAt (W q) (uniformFlowExp g gi hC hK q v)) ∧
      IsOpen (uniformFlowExp g gi hC hK q '' Metric.ball 0 c) ∧
      closure (uniformFlowExp g gi hC hK q '' Metric.ball 0 c)
        ⊆ uniformFlowExp g gi hC hK q '' Metric.closedBall 0 c ∧
      (∀ v : Point n, ‖v‖ < c →
        rncRadialSq (uniformFlowExp g gi hC hK q v - q) ≤ (3 / 2 : ℝ) * rncRadialSq v) ∧
      q ∈ uniformFlowExp g gi hC hK q '' Metric.ball 0 c := by
    intro q hq
    obtain ⟨hchartGerm, hchartOC⟩ := hchart q hq
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro τ hτ v hv
      have hvN : ‖v‖ < rN := lt_trans hv hc_rN
      have hvδ₀ : ‖v‖ < δ₀ := lt_trans hv hc_δ₀
      have hvr₁ : ‖v‖ < r₁ := lt_trans hv hc_r₁
      obtain ⟨hgerm, hWc2⟩ := hchartGerm v hvδ₀
      have hg1 : ∀ a' b', ContDiffAt ℝ 1 (fun y => g y a' b') (uniformFlowExp g gi hC hK q v) :=
        fun a' b' => (hg a' b').contDiffAt.of_le le_top
      have hU : IsUnit (matToCLM (fun a' b' => g (uniformFlowExp g gi hC hK q v) a' b')) :=
        hgnd (uniformFlowExp g gi hC hK q v)
      have hGGi : ∀ pp cc, (∑ bb, g (uniformFlowExp g gi hC hK q v) pp bb
          * gi (uniformFlowExp g gi hC hK q v) bb cc) = if pp = cc then (1 : ℝ) else 0 :=
        fun pp cc => hinvF (uniformFlowExp g gi hC hK q v) pp cc
      have hGiG : ∀ pp cc, (∑ aa, gi (uniformFlowExp g gi hC hK q v) pp aa
          * g (uniformFlowExp g gi hC hK q v) aa cc) = if pp = cc then (1 : ℝ) else 0 :=
        metricInv_left_of_right
          (fun a' b' => g (uniformFlowExp g gi hC hK q v) a' b')
          (fun a' b' => gi (uniformFlowExp g gi hC hK q v) a' b')
          (hgnd (uniformFlowExp g gi hC hK q v))
          (fun pp cc => hinvF (uniformFlowExp g gi hC hK q v) pp cc)
      have hf : ContDiffAt ℝ 2
          (fun x => globalCutoffParametrixWitnessN 1 Θ u a b (W) τ x q)
          (uniformFlowExp g gi hC hK q v) := by
        have hFmul : ContDiffAt ℝ 2 (fun y : Point n => radialCutoff a b y * heatParametrix 1 Θ u τ y)
            (W q (uniformFlowExp g gi hC hK q v)) := by
          apply ContDiffAt.mul
          · exact (radialCutoff_contDiff a b).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
          · exact (heatParametrix_contDiff_space 1 Θ u τ hw).contDiffAt.of_le le_top
        exact hFmul.comp (uniformFlowExp g gi hC hK q v) hWc2
      have hpt : W q (uniformFlowExp g gi hC hK q v) = v := by
        simpa using hgerm.eq_of_nhds
      have hprofilegerm :
          (fun z => globalCutoffParametrixWitnessN 1 Θ u a b (W) τ
              (uniformFlowExp g gi hC hK q z) q)
            =ᶠ[nhds v] (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) := by
        filter_upwards [hgerm] with z hz
        have hz' : W q (uniformFlowExp g gi hC hK q z) = z := hz
        simp only [globalCutoffParametrixWitnessN, hz']
      have hlap : laplaceBeltrami g gi
            (fun p => globalCutoffParametrixWitnessN 1 Θ u a b (W) τ p q)
            (uniformFlowExp g gi hC hK q v)
          = laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
              (uniformFlowPullbackMetricInv g gi hC hK q)
              (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v := by
        have hn := hnat
          (fun x => globalCutoffParametrixWitnessN 1 Θ u a b (W) τ x q)
          q hq v hvN hg1 hf hU hGGi hGiG
        rw [← hn]
        exact QIQTH.VanVleckCancellation.laplaceBeltrami_congr_nhds
          (uniformFlowPullbackMetric g gi hC hK q) (uniformFlowPullbackMetricInv g gi hC hK q)
          _ _ v hprofilegerm
      have htransport :
          heatOp g gi (globalCutoffParametrixWitnessN 1 Θ u a b (W)) τ
              (uniformFlowExp g gi hC hK q v) q
            = radialCutoff a b v * deriv (fun s => heatParametrix 1 Θ u s v) τ
              - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
                  (uniformFlowPullbackMetricInv g gi hC hK q)
                  (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v := by
        simp only [heatOp]
        have hterm1fun :
            (fun s => globalCutoffParametrixWitnessN 1 Θ u a b (W) s
                (uniformFlowExp g gi hC hK q v) q)
              = (fun s => radialCutoff a b v * heatParametrix 1 Θ u s v) := by
          funext s
          simp only [globalCutoffParametrixWitnessN, hpt]
        rw [hterm1fun, deriv_const_mul_field, hlap]
      rw [htransport]
      have hnarrow := hAbound τ hτ q hq v
      have htransfer :
          gaussDdim (3 / 2 * τ) v
            ≤ Real.sqrt (2 / (3 / 2)) ^ n
                * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q) :=
        gaussDdim_le_gaussDdim_chart (c := 3 / 2) (d := 2) (by norm_num) (by norm_num) hτ
          (hdisp q hq v hvr₁)
      have hBτ0 : (0 : ℝ) ≤ B₀ + B₁ * τ := by positivity
      calc |radialCutoff a b v * deriv (fun s => heatParametrix 1 Θ u s v) τ
                - laplaceBeltrami (uniformFlowPullbackMetric g gi hC hK q)
                    (uniformFlowPullbackMetricInv g gi hC hK q)
                    (fun y => radialCutoff a b y * heatParametrix 1 Θ u τ y) v|
          ≤ (B₀ + B₁ * τ) * gaussDdim (3 / 2 * τ) v := hnarrow
        _ ≤ (B₀ + B₁ * τ) * (Sc * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q)) := by
            rw [hSc_def]; exact mul_le_mul_of_nonneg_left htransfer hBτ0
        _ = (B₀' + B₁' * τ) * gaussDdim (2 * τ) (uniformFlowExp g gi hC hK q v - q) := by
            rw [hB0'_def, hB1'_def]; ring
    · intro v hv
      have hvδ₀ : ‖v‖ < δ₀ := lt_of_le_of_lt hv hc_δ₀
      simpa using (hchartGerm v hvδ₀).1.eq_of_nhds
    · intro v hv
      have hvδ₀ : ‖v‖ < δ₀ := lt_of_le_of_lt hv hc_δ₀
      exact (hchartGerm v hvδ₀).2.continuousAt
    · exact (hchartOC c hc0 hc_δ₀).1
    · exact (hchartOC c hc0 hc_δ₀).2
    · intro v hv
      have hvr₁ : ‖v‖ < r₁ := lt_trans hv hc_r₁
      have hd := hdisp q hq v hvr₁
      linarith [hd, rncRadialSq_nonneg v]
    · exact ⟨0, by rw [mem_ball_zero_iff, norm_zero]; exact hc0, uniformFlowExp_zero g gi hC hK q hq⟩
  have hpkg := gatedWitnessN1_hEboundW_le_of_good_CONST g gi hC hK Θ u a b B₀' B₁' ha hab hB0'0 hB1'0 W
    c hbc hgoodC
  exact ⟨a, b, max B₀' B₁', c, ha, hab, le_trans hB0'0 (le_max_left _ _), hbc,
    hpkg.1, hpkg.2.1, hpkg.2.2.1, hpkg.2.2.2⟩

/-! ### (U1) — `gatedWitnessN1_package_open_CONSTRADIUS`: the A3′ package with the radius EXPOSED. -/

/-- **★★★ J4-316 (U1) CAPSTONE — `gatedWitnessN1_package_open_CONSTRADIUS`.**  Exactly
    `GateOpennessExport.gatedWitnessN1_package_open` (the `N = 1` van-Vleck gated witness with the `(0,t]`
    bound + origin gate membership + origin gate-openness), but with the flow-ball radius EXPOSED as the
    constant `c` (with `b < c`) it secretly is, and the gate written literally as
    `fun z => uniformFlowExp g gi hC hK z '' Metric.ball 0 c` — no `.choose`.  This is the drop-in
    replacement for the a₁ chain's package that additionally exposes the constancy the S1 gate-measurability
    slot needs.  NOT `a₁ = R/6`. -/
theorem gatedWitnessN1_package_open_CONSTRADIUS (g gi : Point n → Fin n → Fin n → ℝ)
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
    (hg0 : ∀ i j, g 0 i j = if i = j then (1 : ℝ) else 0) :
    ∃ a b C c : ℝ, 0 < a ∧ a < b ∧ 0 ≤ C ∧ b < c ∧
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
          IsOpen (uniformFlowExp g gi hC hK 0 '' Metric.ball (0 : Point n) c)) := by
  obtain ⟨ρ0, hρ0, C0, hC0, hb0⟩ :=
    hCoeffU0_vanVleck g gi hg hC hK hgnd hgsymm hinvF hframeK
      (transportOp (vanVleck g) g gi) (hw 0) hdg0 hg0
  obtain ⟨ρ1, hρ1, C1, hC1, hb1⟩ :=
    uniformCoeffLinear_bound g gi hg hC hK hgnd hgsymm hinvF hframeK (vanVleck g)
      (fun j => transportCoeff (transportOp (vanVleck g) g gi) (j + 1)) (hw 1)
  set ρ_c : ℝ := min ρ0 ρ1 with hρc_def
  have hρc0 : 0 < ρ_c := lt_min hρ0 hρ1
  obtain ⟨a, b, C, c, ha, hab, hC0', hbc, hbound, hgate, hmemS, hopenS⟩ :=
    gatedWitnessN1_hEboundW_le_lin_CONST g gi hg hC hK hgnd hgsymm hinvF hframeK
      (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) hw
      ρ_c C0 C1 hρc0 hC0 hC1
      (fun q hq v hv => hb0 q hq v (lt_of_lt_of_le hv (min_le_left _ _)))
      (fun q hq v hv => hb1 q hq v (lt_of_lt_of_le hv (min_le_right _ _)))
  refine ⟨a, b, C, c, ha, hab, hC0', hbc, hbound, ?_, ?_⟩
  · intro h0; exact hmemS 0 h0
  · intro h0; exact hopenS 0 h0

/-! ### (U2) — S1 (`tripleHEmeas`) at the exposed CONSTANT gate; `Measurable cf` dissolved. -/

/-- **★★ J4-316 (U2) — `tripleHEmeas_AT_CONSTRADIUS_GATE`.**  S1 (the base joint strong measurability
    `HEmeasBorelAudit.tripleHEmeas`) at the CONSTANT flow-ball gate `fun z => φ_z '' ball 0 c` exposed by
    (U1), from geometry alone: there is a reach `δ₀ > 0` (the JET reach of `tripleHEmeas_flowball_geometry`)
    such that `c < δ₀ → S1`.  This is exactly `S1TripleHEmeasGate.tripleHEmeas_flowball_geometry`
    specialized to the single constant `c` — the varying-gate S1 residue `Measurable cf` has DISSOLVED to
    `measurable_const` because `cf = fun _ => c`.  The compatibility `c < δ₀` (the U1 chart reach `c < ρc`
    vs the JET reach `δ₀` are a-priori different) is carried honestly as the conclusion's ANTECEDENT.  NOT
    `a₁ = R/6`. -/
theorem tripleHEmeas_AT_CONSTRADIUS_GATE (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (a b c : ℝ) (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgiC : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (hu : ∀ k, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (transportCoeff (transportOp (vanVleck g) g gi) k))
    (hgiMeas : ∀ i j : Fin n, Measurable (fun p : Point n => gi p i j))
    (hchr : ∀ k i j : Fin n, Measurable (fun p : Point n => christoffel g gi k i j p)) :
    ∃ δ₀ > (0 : ℝ), c < δ₀ →
      QIQTH.HEmeasBorelAudit.tripleHEmeas g gi
        (vanVleckGatedWitness g gi hC hK
          (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) a b) := by
  obtain ⟨δ₀, hδ₀pos, hspec⟩ :=
    tripleHEmeas_flowball_geometry hn g gi hC hK a b ha hab hg hgiC hgpos hu hgiMeas hchr
  exact ⟨δ₀, hδ₀pos, fun hcδ => hspec c hbc hcδ⟩

/-! ### (U3) — the bundled ingredients for the future v3-export. -/

/-- **★★★ J4-316 (U3) — `constRadius_package_and_S1`.**  The two load-bearing ingredients the strengthened
    (v3) provider will consume, bundled: (i) the (U1) constant-radius package (bound + origin gate
    membership + origin gate-openness) for the literal gate `fun z => φ_z '' ball 0 c`, and (ii) the (U2)
    S1 fact at that SAME gate (`c < δ₀ → tripleHEmeas`).  No `∀`-gate `hEmeas` artefact and no `.choose`
    radius; the S1 slot is now a geometry-only fact modulo the honest smallness `c < δ₀`.  NOT `a₁ = R/6`. -/
theorem constRadius_package_and_S1 (hn : 0 < n) (g gi : Point n → Fin n → Fin n → ℝ)
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
    ∃ a b C c : ℝ, ∃ δ₀ : ℝ,
      0 < a ∧ a < b ∧ 0 ≤ C ∧ b < c ∧ 0 < δ₀ ∧
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
      ∧ (c < δ₀ →
          QIQTH.HEmeasBorelAudit.tripleHEmeas g gi
            (vanVleckGatedWitness g gi hC hK
              (fun z => uniformFlowExp g gi hC hK z '' Metric.ball (0 : Point n) c) a b)) := by
  obtain ⟨a, b, C, c, ha, hab, hC0, hbc, hbound, hmemS0, hopenS0⟩ :=
    gatedWitnessN1_package_open_CONSTRADIUS g gi hg hC hK hgnd hgsymm hinvF hframeK hw hdg0 hg0
  obtain ⟨δ₀, hδ₀pos, hS1⟩ :=
    tripleHEmeas_AT_CONSTRADIUS_GATE hn g gi hC hK a b c ha hab hbc hg hgiC hgpos hu hgiMeas hchr
  exact ⟨a, b, C, c, δ₀, ha, hab, hC0, hbc, hδ₀pos, hbound, hmemS0, hopenS0, hS1⟩

end QIQTH.ConstRadiusGateExport

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.ConstRadiusGateExport
#print axioms gatedWitnessN1_hEboundW_le_of_good_CONST
#print axioms gatedWitnessN1_hEboundW_le_lin_CONST
#print axioms gatedWitnessN1_package_open_CONSTRADIUS
#print axioms tripleHEmeas_AT_CONSTRADIUS_GATE
#print axioms constRadius_package_and_S1
end AxiomChecks
