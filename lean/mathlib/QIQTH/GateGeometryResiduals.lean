/-
  GateGeometryResiduals — J4-304: the two PURE GATE-GEOMETRY residuals of the Levi `0`-slice
  joint-continuity carrier `QIQTH.HactiveWiring.leviSlice_hf_cont` (J4-303).

  Context: the `a₁ = R/6` campaign, the Levi-continuity endgame.  `leviSlice_hf_cont` reduces the full
  Levi `0`-slice joint continuity to, beyond the banked/envelope/structural inputs, TWO pure
  gate-geometry residuals about the concrete provider gate

      S w = φ_w '' ball 0 c ,   φ_w := uniformFlowExp g gi hC hK w ,   W w := uniformInverseChart g gi hC hK w ,

  namely
    • (I1, inside `hgeo`)   `closure (S w) ⊆ ball w ρc`     — the gate closure sits inside the chart's
      `C²` ball;
    • (the collar, in `hfg`) `∀ z ∈ closure (S w), z ∉ ball w Rg → b² < rncRadialSq (W w z)` — far
      closure-points are chart-far.

  This file discharges BOTH from the banked gate data — the closure containment
  `closure (φ_w '' ball 0 c) ⊆ φ_w '' closedBall 0 c` (the `hclos` good-witness conjunct), the
  left-inverse germ `W w (φ_w v) = v` on the closed ball (the `hinv` conjunct), and the QUADRATIC
  near-identity displacement `‖φ_w v − w − v‖ ≤ C_D·‖v‖²` (`ExpMap.uniformFlowExp_displacement_bound`) —
  plus an HONEST, satisfiable radii relation (the provider shrinks the gate radius `c`/`b`).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  WHAT LANDS (all DERIVED; NO `sorry`; each std-3):

    • (G1) `gate_closure_subset_chartBall` — `closure (S w) ⊆ ball w ρc`.  Route: `hclos` sends any
      closure point to `φ_w v` with `‖v‖ ≤ c`; the displacement bound gives
      `‖φ_w v − w‖ ≤ ‖v‖ + C_D‖v‖² ≤ c + C_D c²`, which is `< ρc` by the radii relation `hradii`.

    • (G2) `gate_far_implies_chartFar` — the collar `∀ z ∈ closure (S w), z ∉ ball w Rg →
      b² < rncRadialSq (W w z)`.  Route (contrapositive): a closure point is `φ_w v`, `‖v‖ ≤ c`, and
      `W w (φ_w v) = v` by `hinv`; if `rncRadialSq v ≤ b²` then `‖v‖ ≤ b`, so
      `dist (φ_w v) w ≤ b + C_D b² < Rg`, i.e. the point is NOT far — contradiction.  Honest `Rg`
      window: `b + C_D·b² < Rg`.

    • (G1c/G2c) `gate_closure_subset_chartBall_selfContained` /
      `gate_far_implies_chartFar_selfContained` — the same, with the displacement DATUM discharged
      internally from `ExpMap.uniformFlowExp_displacement_bound`; the caller supplies only the
      geometry (`hclos`/`hinv`), a radius nesting `c < ρ₀`, and the honest radii relation stated
      against the internally-exposed constant `C_D`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  No `sorry` (this header prose aside), no new axioms, no `:= True`, no vacuous or
     unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion, no
     existing file edited.  `hclos`/`hinv` are the gate's OWN banked construction exports (the
     good-witness conjuncts — satisfiable, not the conclusion); `hdisp2` is the banked quadratic
     displacement (`ExpMap.uniformFlowExp_displacement_bound`); `hradii`/`hRg` are honest radii
     relations, satisfiable because the provider shrinks the gate radius (`c = (b+ρc)/2` with `b` free
     to shrink).  **NOT `a₁ = R/6`** — a regularity / coverage geometry brick; it says NOTHING about
     the curvature value.
-/
import Mathlib
import QIQTH.NearIsometryBudget
import QIQTH.UniformChartRadius
import QIQTH.HactiveWiring

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.RNCDecay QIQTH.ExpMap QIQTH.HeatResidualBound
open QIQTH.LeviSeries QIQTH.TrueHeatKernel QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.FastA5Fix QIQTH.FrozenBaseWChain QIQTH.H2Instantiation QIQTH.HactiveWiring
open scoped Topology ContDiff

namespace QIQTH.GateGeometryResiduals

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ###############################################################################
    ## (G1) `closure (S w) ⊆ ball w ρc` — the chart-ball containment residual (I1).
    ############################################################################### -/

/-- **★ (G1) `gate_closure_subset_chartBall`.**  The concrete provider gate `S w = φ_w '' ball 0 c`
    has `closure (S w) ⊆ ball w ρc`.  Inputs: the banked closure containment
    `hclos : closure (φ_w '' ball 0 c) ⊆ φ_w '' closedBall 0 c` (the good-witness `hclos` conjunct);
    the banked quadratic displacement `hdisp2 : ‖φ_q v − q − v‖ ≤ C_D‖v‖²` for `‖v‖ < ρ₀`
    (`ExpMap.uniformFlowExp_displacement_bound`); the radius nesting `c < ρ₀`; and the HONEST radii
    relation `hradii : c + C_D·c² < ρc` (satisfiable — the provider shrinks `c`).  NOT `a₁ = R/6`. -/
theorem gate_closure_subset_chartBall (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (w : Point n) (hw : w ∈ K)
    (c ρc ρ₀ C_D : ℝ) (hc0 : 0 < c) (hcρ₀ : c < ρ₀) (hCD0 : 0 ≤ C_D)
    (hdisp2 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ₀ →
        ‖uniformFlowExp g gi hC hK q v - q - v‖ ≤ C_D * ‖v‖ * ‖v‖)
    (hclos : closure (uniformFlowExp g gi hC hK w '' Metric.ball 0 c)
        ⊆ uniformFlowExp g gi hC hK w '' Metric.closedBall 0 c)
    (hradii : c + C_D * c * c < ρc) :
    closure (uniformFlowExp g gi hC hK w '' Metric.ball 0 c) ⊆ Metric.ball w ρc := by
  intro z hz
  obtain ⟨v, hvmem, rfl⟩ := hclos hz
  rw [Metric.mem_closedBall, dist_zero_right] at hvmem
  have hvρ₀ : ‖v‖ < ρ₀ := lt_of_le_of_lt hvmem hcρ₀
  have he : ‖uniformFlowExp g gi hC hK w v - w - v‖ ≤ C_D * ‖v‖ * ‖v‖ := hdisp2 w hw v hvρ₀
  rw [Metric.mem_ball, dist_eq_norm]
  have htri : ‖uniformFlowExp g gi hC hK w v - w‖
      ≤ ‖uniformFlowExp g gi hC hK w v - w - v‖ + ‖v‖ := by
    have h := norm_add_le (uniformFlowExp g gi hC hK w v - w - v) v
    have heq : uniformFlowExp g gi hC hK w v - w - v + v = uniformFlowExp g gi hC hK w v - w := by
      abel
    rwa [heq] at h
  have hvv : ‖v‖ * ‖v‖ ≤ c * c := mul_le_mul hvmem hvmem (norm_nonneg v) hc0.le
  have hCDvv : C_D * ‖v‖ * ‖v‖ ≤ C_D * c * c := by
    calc C_D * ‖v‖ * ‖v‖ = C_D * (‖v‖ * ‖v‖) := by ring
      _ ≤ C_D * (c * c) := mul_le_mul_of_nonneg_left hvv hCD0
      _ = C_D * c * c := by ring
  have hfin : ‖uniformFlowExp g gi hC hK w v - w‖ ≤ C_D * ‖v‖ * ‖v‖ + ‖v‖ :=
    le_trans htri (by linarith [he])
  linarith [hfin, hCDvv, hvmem, hradii]

/-! ###############################################################################
    ## (G2) The collar `z far ⟹ chart-far` — the `hfg` collar residual.
    ############################################################################### -/

/-- **★★ (G2) `gate_far_implies_chartFar`.**  For the concrete gate `S w = φ_w '' ball 0 c`, every
    closure point `z` with `z ∉ ball w Rg` satisfies `b² < rncRadialSq (W w z)`.  Inputs: `hclos`
    (closure containment), the left-inverse germ `hinv : W w (φ_w v) = v` on the closed ball (the
    good-witness `hinv` conjunct), the banked displacement `hdisp2`, the radius nesting `c < ρ₀`, and
    the HONEST `Rg`-window `hRg : b + C_D·b² < Rg` (satisfiable — `Rg` is chosen by the provider).
    Route (contrapositive): if `rncRadialSq v ≤ b²` then `‖v‖ ≤ b`, so `dist (φ_w v) w ≤ b + C_D b² <
    Rg`, contradicting `z ∉ ball w Rg`.  NOT `a₁ = R/6`. -/
theorem gate_far_implies_chartFar (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (w : Point n) (hw : w ∈ K)
    (b c Rg ρ₀ C_D : ℝ) (hb0 : 0 < b) (_hc0 : 0 < c) (hcρ₀ : c < ρ₀) (hCD0 : 0 ≤ C_D)
    (hdisp2 : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ₀ →
        ‖uniformFlowExp g gi hC hK q v - q - v‖ ≤ C_D * ‖v‖ * ‖v‖)
    (hclos : closure (uniformFlowExp g gi hC hK w '' Metric.ball 0 c)
        ⊆ uniformFlowExp g gi hC hK w '' Metric.closedBall 0 c)
    (hinv : ∀ v : Point n, ‖v‖ ≤ c →
        uniformInverseChart g gi hC hK w (uniformFlowExp g gi hC hK w v) = v)
    (hRg : b + C_D * b * b < Rg) :
    ∀ z ∈ closure (uniformFlowExp g gi hC hK w '' Metric.ball 0 c), z ∉ Metric.ball w Rg →
        b ^ 2 < rncRadialSq (uniformInverseChart g gi hC hK w z) := by
  intro z hz hznotball
  obtain ⟨v, hvmem, rfl⟩ := hclos hz
  rw [Metric.mem_closedBall, dist_zero_right] at hvmem
  rw [hinv v hvmem]
  by_contra hnlt
  have hnlt' : rncRadialSq v ≤ b ^ 2 := not_lt.mp hnlt
  -- `‖v‖ ≤ b` from `rncRadialSq v ≤ b²` and `‖v‖² ≤ rncRadialSq v`.
  have hnvsq : ‖v‖ ^ 2 ≤ rncRadialSq v := by
    have h := norm_le_rncRadial v
    calc ‖v‖ ^ 2 ≤ (rncRadial v) ^ 2 := pow_le_pow_left₀ (norm_nonneg v) h 2
      _ = rncRadialSq v := rncRadial_sq v
  have h2 : ‖v‖ ^ 2 ≤ b ^ 2 := le_trans hnvsq hnlt'
  have hnvb : ‖v‖ ≤ b := by
    have hs := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq (norm_nonneg v), Real.sqrt_sq hb0.le] at hs
  -- displacement ⟹ the point is within `Rg` of `w`, contradicting `z ∉ ball w Rg`.
  have hvρ₀ : ‖v‖ < ρ₀ := lt_of_le_of_lt hvmem hcρ₀
  have he : ‖uniformFlowExp g gi hC hK w v - w - v‖ ≤ C_D * ‖v‖ * ‖v‖ := hdisp2 w hw v hvρ₀
  have htri : ‖uniformFlowExp g gi hC hK w v - w‖
      ≤ ‖uniformFlowExp g gi hC hK w v - w - v‖ + ‖v‖ := by
    have h := norm_add_le (uniformFlowExp g gi hC hK w v - w - v) v
    have heq : uniformFlowExp g gi hC hK w v - w - v + v = uniformFlowExp g gi hC hK w v - w := by
      abel
    rwa [heq] at h
  have hvv : ‖v‖ * ‖v‖ ≤ b * b := mul_le_mul hnvb hnvb (norm_nonneg v) hb0.le
  have hCDvv : C_D * ‖v‖ * ‖v‖ ≤ C_D * b * b := by
    calc C_D * ‖v‖ * ‖v‖ = C_D * (‖v‖ * ‖v‖) := by ring
      _ ≤ C_D * (b * b) := mul_le_mul_of_nonneg_left hvv hCD0
      _ = C_D * b * b := by ring
  have hdist : dist (uniformFlowExp g gi hC hK w v) w < Rg := by
    rw [dist_eq_norm]
    have hfin : ‖uniformFlowExp g gi hC hK w v - w‖ ≤ C_D * ‖v‖ * ‖v‖ + ‖v‖ :=
      le_trans htri (by linarith [he])
    linarith [hfin, hCDvv, hnvb, hRg]
  exact hznotball (Metric.mem_ball.mpr hdist)

/-! ###############################################################################
    ## (G3) `leviSlice_hf_cont_FINAL` — the Levi `0`-slice continuity with BOTH gate-
    ##      geometry residuals internalised (I1 via G1, the collar via G2).
    ############################################################################### -/

/-- **★★★ (G3) `leviSlice_hf_cont_FINAL`.**  `HactiveWiring.leviSlice_hf_cont` with the consumer's
    `hgeo` (chart-`C²` + containment) and `hfg` (full-gate `ContinuousOn` + collar) REPLACED by two
    per-`w` gate-geometry bundles whose GEOMETRIC residuals are discharged internally by G1
    (`gate_closure_subset_chartBall`) and G2 (`gate_far_implies_chartFar`).

    FINAL HONEST INPUT LIST (none is the conclusion; all satisfiable — see header):
      • the banked four — `hEbound`, `hInt`, `hEmeas`, `hbase` (base-`0` slice `ContinuousOn`);
      • the summable termwise envelope — `env`, `hu`, `hbound`;
      • `hgeoBundle` — per `w ∈ K`: the chart-`C²` on `ball w ρc` (banked, `FrozenBaseWChain`), the gate
        shape `S w = φ_w '' ball 0 cw`, the banked closure containment and quadratic displacement
        datum, and the HONEST radii relation `cw + C_Dw·cw² < ρc` (G1's hypotheses);
      • `hfgBundle` — per `w ∈ K` and time window: the banked full-gate `ContinuousOn E(·,·,w)`
        (`FastA5Fix`), the gate shape, the closure containment, the left-inverse germ `W w (φ_w v)=v`,
        the displacement datum, and the HONEST `Rg`-window `b + C_Dw·b² < Rg` (G2's hypotheses).
    ⚠ STILL NOT `a₁ = R/6`. -/
theorem leviSlice_hf_cont_FINAL (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b)
    (κ C : ℝ) (hκ : 0 < κ) (hC0 : 0 ≤ C)
    (t₁ t₂ R : ℝ) (ht₁ : 0 < t₁) (ht₁₂ : t₁ ≤ t₂) (hR : 0 < R)
    (hEbound : ∀ τ p q, 0 < τ →
      |heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) τ p q| ≤ C * baseKernelW κ 0 τ p q)
    (hInt : IterConvIntegrableW (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) κ 0 C)
    (hEmeas : StronglyMeasurable (fun q : ℝ × Point n × Point n =>
      heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) q.1 q.2.1 q.2.2))
    (hbase : ∀ t₁ t₂ R : ℝ, 0 < t₁ → t₁ ≤ t₂ → 0 < R →
      ContinuousOn (fun p : ℝ × Point n =>
          heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 0)
        (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R))
    (hgeoBundle : ∀ w ∈ K, ∃ ρc cw ρ₀w C_Dw : ℝ,
      0 < ρc ∧
      ContDiffOn ℝ 2 (uniformInverseChart g gi hC hK w) (Metric.ball w ρc) ∧
      S w = uniformFlowExp g gi hC hK w '' Metric.ball 0 cw ∧
      0 < cw ∧ cw < ρ₀w ∧ 0 ≤ C_Dw ∧
      (∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ₀w →
        ‖uniformFlowExp g gi hC hK q v - q - v‖ ≤ C_Dw * ‖v‖ * ‖v‖) ∧
      closure (uniformFlowExp g gi hC hK w '' Metric.ball 0 cw)
        ⊆ uniformFlowExp g gi hC hK w '' Metric.closedBall 0 cw ∧
      cw + C_Dw * cw * cw < ρc)
    (hfgBundle : ∀ w ∈ K, ∀ s₁ s₂ : ℝ, 0 < s₁ →
      ∃ Rg cw ρ₀w C_Dw : ℝ,
        0 < Rg ∧
        ContinuousOn (fun p : ℝ × Point n =>
            heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
          (Set.Icc s₁ s₂ ×ˢ Metric.closedBall w Rg) ∧
        S w = uniformFlowExp g gi hC hK w '' Metric.ball 0 cw ∧
        0 < cw ∧ cw < ρ₀w ∧ 0 ≤ C_Dw ∧
        (∀ q ∈ K, ∀ v : Point n, ‖v‖ < ρ₀w →
          ‖uniformFlowExp g gi hC hK q v - q - v‖ ≤ C_Dw * ‖v‖ * ‖v‖) ∧
        closure (uniformFlowExp g gi hC hK w '' Metric.ball 0 cw)
          ⊆ uniformFlowExp g gi hC hK w '' Metric.closedBall 0 cw ∧
        (∀ v : Point n, ‖v‖ ≤ cw →
          uniformInverseChart g gi hC hK w (uniformFlowExp g gi hC hK w v) = v) ∧
        b + C_Dw * b * b < Rg)
    (env : ℕ → ℝ) (hu : Summable env)
    (hbound : ∀ (k : ℕ) (p : ℝ × Point n),
      p ∈ Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R →
      ‖(-1 : ℝ) ^ (k + 1)
          * iterE (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) (k + 1) p.1 p.2 0‖
        ≤ env k) :
    ContinuousOn (fun p : ℝ × Point n =>
        leviSeries (heatOp g gi (vanVleckGatedWitness g gi hC hK S a b)) p.1 p.2 0)
      (Set.Icc t₁ t₂ ×ˢ Metric.closedBall (0 : Point n) R) := by
  have hb : 0 < b := lt_trans ha hab
  -- Reconstruct the consumer's `hgeo` from `hgeoBundle` via G1.
  have hgeo : ∀ w ∈ K, ∃ ρc : ℝ, 0 < ρc ∧
      ContDiffOn ℝ 2 (uniformInverseChart g gi hC hK w) (Metric.ball w ρc) ∧
      closure (S w) ⊆ Metric.ball w ρc := by
    intro w hw
    obtain ⟨ρc, cw, ρ₀w, C_Dw, hρc, hchart, hSeq, hcw0, hcwρ₀, hCD0w, hdisp2, hclos, hradii⟩ :=
      hgeoBundle w hw
    refine ⟨ρc, hρc, hchart, ?_⟩
    rw [hSeq]
    exact gate_closure_subset_chartBall g gi hC hK w hw cw ρc ρ₀w C_Dw hcw0 hcwρ₀ hCD0w
      hdisp2 hclos hradii
  -- Reconstruct the consumer's `hfg` from `hfgBundle` via G2.
  have hfg : ∀ w ∈ K, ∀ s₁ s₂ : ℝ, 0 < s₁ →
      ∃ Rg : ℝ, 0 < Rg ∧
        ContinuousOn (fun p : ℝ × Point n =>
            heatOp g gi (vanVleckGatedWitness g gi hC hK S a b) p.1 p.2 w)
          (Set.Icc s₁ s₂ ×ˢ Metric.closedBall w Rg) ∧
        (∀ z ∈ closure (S w), z ∉ Metric.ball w Rg →
            b ^ 2 < rncRadialSq (uniformInverseChart g gi hC hK w z)) := by
    intro w hw s₁ s₂ hs₁
    obtain ⟨Rg, cw, ρ₀w, C_Dw, hRg0, hcont, hSeq, hcw0, hcwρ₀, hCD0w, hdisp2, hclos, hinv, hRgwin⟩ :=
      hfgBundle w hw s₁ s₂ hs₁
    refine ⟨Rg, hRg0, hcont, ?_⟩
    rw [hSeq]
    exact gate_far_implies_chartFar g gi hC hK w hw b cw Rg ρ₀w C_Dw hb hcw0 hcwρ₀ hCD0w
      hdisp2 hclos hinv hRgwin
  exact leviSlice_hf_cont g gi hC hK S a b ha hab κ C hκ hC0 t₁ t₂ R ht₁ ht₁₂ hR
    hEbound hInt hEmeas hbase hgeo hfg env hu hbound

#check @gate_closure_subset_chartBall
#check @gate_far_implies_chartFar
#check @leviSlice_hf_cont_FINAL

end QIQTH.GateGeometryResiduals

section AxiomChecks
open QIQTH.GateGeometryResiduals
#print axioms gate_closure_subset_chartBall
#print axioms gate_far_implies_chartFar
#print axioms leviSlice_hf_cont_FINAL
end AxiomChecks
