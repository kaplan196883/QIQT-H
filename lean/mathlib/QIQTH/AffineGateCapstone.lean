/-
  AffineGateCapstone — J4-377: the 3-REGION ∃-CAPSTONE assembly of `AffineGateBound`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is ONE
  ASSEMBLY / GLUE brick of the (still CONDITIONAL) `a₁ = R/6` heat-kernel campaign.  It takes the two
  banked geometric LEGS of the affine on-gate width-`4/3` quadratic bound — the PLATEAU leg
  (`PullbackAffineBallLeg.gatedHeatOp_pullbackAffine_onBallPlateau`, J4-374) and the ANNULUS leg
  (`AnnulusAmbientTransfer.gatedHeatOp_affine_onAnnulus`, J4-376) — plus the EXTERIOR off-support
  vanishing, and STITCHES them into the single predicate `HgateAffineRepair.AffineGateBound`.  The
  quantifier `p ∈ closure (S q)` is parametrized (C1) as the flow-exp image of a closed ball, the
  three radial regions `r²<a²`, `a²≤r²≤b²`, `r²>b²` are dispatched (C3) to the plateau leg, the annulus
  leg, and the exterior vanishing (C2) respectively.  NO `sorry` (header prose excepted), NO new axioms,
  NO `:= True`, NO vacuous / unsatisfiable hypothesis, NONE equal to (or trivially yielding) the
  conclusion, NO existing file edited, nothing committed.  `a₁ = R/6` stays CONDITIONAL on the whole
  convergence / geometric-wiring stack AND on the surviving LABELLED inputs (here: the two uniform leg
  bounds `hplat`/`hann`, which carry the geometric data piles, and the banked chart facts).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## DELIVERABLES.
  •  (C1) `expPoint_of_mem_closure` — the closure parametrization: for the concrete gate
     `S q = φ_q '' ball 0 c`, every `p ∈ closure (S q)` is `p = φ_q v` with `‖v‖ ≤ c` (via the banked
     closure ⊆ `φ_q '' closedBall 0 c` fact of the `_of_good` shell).
  •  (C2) `gatedHeatOp_eq_zero_exterior` — the EXTERIOR vanishing: where the chart-inverse radial
     coordinate exceeds `b²` the cutoff `radialCutoff a b` kills the witness near `p`, so both the time
     and space germs of the gated kernel vanish and `heatOp = 0` (the LEG-3 collar logic of `_of_good`,
     promoted to a standalone lemma).  The exterior collar is NOT empty (it is `b < ‖v‖ ≤ c`), but the
     gated heatOp is `0` there.
  •  (C3) `affineGateBound_of_legs` — ★★★ THE CAPSTONE: from the two UNIFORM leg bounds (`hplat`,
     `hann`, sharing the concrete gate geometry), the banked chart facts (`hWpt`/`hWcont`/`hSopen`/
     `hSmem`/`hSclos`/`hcb`), and C1+C2, assemble `AffineGateBound g gi K S (…N1 witness…)` with the
     coefficient pair `(max P₀a P₀b, max P₁a P₁b)` (the two legs' pairs maxed).

  ## SATISFIABILITY / HONESTY.  The leg carries `hplat`/`hann` are SATISFIABLE — they are exactly the
  banked leg outputs (`gatedHeatOp_pullbackAffine_onBallPlateau` / `gatedHeatOp_affine_onAnnulus`)
  specialized to a uniform coefficient pair over the gate; the residual work to instantiate them
  unconditionally is the geometric data-pile discharge (the flow-frame uniforms), NOT this glue.  Every
  chart carry (`hWpt`/`hWcont`/`hSopen`/`hSmem`/`hSclos`) is a banked property of the `_of_good` gate
  construction.  NONE equals the conclusion.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HgateAffineRepair
import QIQTH.PullbackAffineBallLeg
import QIQTH.AnnulusAmbientTransfer
import QIQTH.GlobalWitnessHunif
import QIQTH.GlobalHunifAssembly
import QIQTH.CutoffAnnulusSupport
import QIQTH.RNCDecay
import QIQTH.OrderNResidual
import QIQTH.SmoothCutoff
import QIQTH.UniformFlowNondeg
import QIQTH.HrawCampaignOne

open Set Filter
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.HeatResidualBound QIQTH.ResidueBound
open QIQTH.RNCDecay QIQTH.ExpMap QIQTH.FlatHeatEquation QIQTH.TrueHeatKernel
open scoped Topology BigOperators

namespace QIQTH.AffineGateCapstone

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (C1) — the closure parametrization of the concrete gate.
    ############################################################################### -/

/-- **★ (C1) — `expPoint_of_mem_closure`.**  THE CLOSURE PARAMETRIZATION.  For the concrete gate
    `S q = φ_q '' ball 0 c` (`φ_q = uniformFlowExp g gi hC hK q`), whose closure is contained in the
    flow-exp image of the CLOSED ball (the banked `_of_good` closure fact `hclos`), every point of
    `closure (S q)` is the flow-exp image of some `v` with `‖v‖ ≤ c`.  This is the honest promotion of
    the `hclos`/`Metric.mem_closedBall` decomposition buried inside the compiled `_of_good` cover
    builder.  NOT `a₁ = R/6`. -/
theorem expPoint_of_mem_closure (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) {S : Point n → Set (Point n)}
    {q : Point n} {c : ℝ} {p : Point n}
    (hclos : closure (S q) ⊆ uniformFlowExp g gi hC hK q '' Metric.closedBall 0 c)
    (hp : p ∈ closure (S q)) :
    ∃ v : Point n, ‖v‖ ≤ c ∧ p = uniformFlowExp g gi hC hK q v := by
  obtain ⟨v, hv, hvp⟩ := hclos hp
  rw [Metric.mem_closedBall, dist_zero_right] at hv
  exact ⟨v, hv, hvp.symm⟩

/-! ###############################################################################
    ### (C2) — the exterior vanishing leg.
    ############################################################################### -/

/-- **★ (C2) — `gatedHeatOp_eq_zero_exterior`.**  THE EXTERIOR VANISHING.  Where the chart-inverse
    radial coordinate exceeds the cutoff top, `b² < rncRadialSq (W q p)`, the smooth cutoff
    `radialCutoff a b (W q p)` is `0`, so the `N = 1` witness
    `globalCutoffParametrixWitnessN 1 Θ u a b W` vanishes at `p`; by continuity of `W q` it vanishes on
    a whole neighbourhood of `p` (the preimage of the open `{w | b² < rncRadialSq w}`).  Both the time
    germ (the cutoff is `τ`-independent) and the space germ of the GATED kernel are therefore `0`
    (`gatedKernel` is either the witness or `0`), and `heatOp_eq_zero_of_locally_zero` gives
    `heatOp = 0`.  This is the LEG-3 collar logic of the compiled `_of_good` cover builder, promoted to
    a standalone lemma.  NOT `a₁ = R/6`. -/
theorem gatedHeatOp_eq_zero_exterior (g gi : Point n → Fin n → Fin n → ℝ)
    (K : Set (Point n)) (S : Point n → Set (Point n))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b : ℝ) (W : Point n → Point n → Point n)
    (τ : ℝ) (p q : Point n) (ha : 0 < a) (hab : a < b)
    (hcontp : ContinuousAt (W q) p)
    (hb2 : b ^ 2 < rncRadialSq (W q p)) :
    heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b W)) τ p q = 0 := by
  have hNnhds : (W q) ⁻¹' {w : Point n | b ^ 2 < rncRadialSq w} ∈ nhds p :=
    hcontp.preimage_mem_nhds ((isOpen_rncRadialSq_gt (b ^ 2)).mem_nhds hb2)
  -- the gated kernel vanishes wherever the chart-inverse radial coordinate exceeds `b²`.
  have hgz : ∀ (s : ℝ) (p' : Point n), b ^ 2 < rncRadialSq (W q p') →
      gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b W) s p' q = 0 := by
    intro s p' hp'
    have hH : globalCutoffParametrixWitnessN 1 Θ u a b W s p' q = 0 := by
      simp only [globalCutoffParametrixWitnessN]
      rw [radialCutoff_eq_zero ha hab (le_of_lt hp'), zero_mul]
    simp only [gatedKernel]
    split_ifs <;> first | exact hH | rfl
  refine QIQTH.HeatResidualBound.heatOp_eq_zero_of_locally_zero g gi
    (gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b W)) τ p q ?_ ?_
  · -- time germ at `p` (holds for all `t`, the set-gate is `τ`-independent).
    exact Filter.Eventually.of_forall (fun t => hgz t p hb2)
  · -- space germ: `0` on the neighbourhood `hNnhds`.
    filter_upwards [hNnhds] with p' hp'
    have hp'2 : b ^ 2 < rncRadialSq (W q p') := hp'
    exact hgz τ p' hp'2

/-! ###############################################################################
    ### (C3) — ★★★ the 3-region ∃-capstone assembly.
    ############################################################################### -/

/-- **★★★ (C3) — `affineGateBound_of_legs`.**  THE 3-REGION CAPSTONE.  Assembles
    `HgateAffineRepair.AffineGateBound g gi K S (globalCutoffParametrixWitnessN 1 Θ u a b W)
    (max P₀a P₀b) (max P₁a P₁b)` from the two UNIFORM geometric legs and the exterior vanishing, over
    the concrete gate `S q = φ_q '' ball 0 (c q)`.

    Structure: `intro τ hτ q hq p hp`; (C1) parametrizes `p = φ_q v` with `‖v‖ ≤ c q`; a three-way
    `by_cases` on `rncRadialSq v` vs `a²` and `b²` dispatches:
    •  `r² < a²`  (PLATEAU) → `hplat` (the ball leg), after discharging the gate-neighbourhood from
       `r² ≤ b² ⟹ ‖v‖ ≤ b < c q ⟹ φ_q v ∈ S q` (open);
    •  `a² ≤ r² ≤ b²`  (ANNULUS) → `hann` (the annulus leg), same neighbourhood discharge;
    •  `b² < r²`  (EXTERIOR) → `gatedHeatOp_eq_zero_exterior` (C2), via `W q (φ_q v) = v` (`hWpt`) and
       continuity (`hWcont`); the LHS is `0 ≤` the nonnegative RHS.
    The two legs' coefficient pairs are unified by `max` (monotonicity of the affine factor against the
    nonnegative envelope).

    The carries `hplat`/`hann` are the SATISFIABLE banked leg outputs specialized to a uniform pair
    over the gate; `hWpt`/`hWcont`/`hSopen`/`hSmem`/`hSclos`/`hcb` are banked properties of the
    `_of_good` gate construction.  NONE equals the conclusion.  NOT `a₁ = R/6`. -/
theorem affineGateBound_of_legs (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a' b' c', ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a' b' c' y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n))
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (a b : ℝ) (W : Point n → Point n → Point n)
    (c : Point n → ℝ) (ha : 0 < a) (hab : a < b)
    (P₀a P₁a P₀b P₁b : ℝ)
    (hP₀a : 0 ≤ P₀a) (hP₁a : 0 ≤ P₁a) (hP₀b : 0 ≤ P₀b) (hP₁b : 0 ≤ P₁b)
    -- gate geometry (banked from the `_of_good` `S q = φ_q '' ball 0 (c q)` construction):
    (hcb : ∀ q ∈ K, b < c q)
    (hSopen : ∀ q ∈ K, IsOpen (S q))
    (hSmem : ∀ q ∈ K, ∀ v : Point n, ‖v‖ < c q → uniformFlowExp g gi hC hK q v ∈ S q)
    (hSclos : ∀ q ∈ K,
        closure (S q) ⊆ uniformFlowExp g gi hC hK q '' Metric.closedBall 0 (c q))
    -- banked chart facts (for the exterior vanishing):
    (hWpt : ∀ q ∈ K, ∀ v : Point n, ‖v‖ ≤ c q →
        W q (uniformFlowExp g gi hC hK q v) = v)
    (hWcont : ∀ q ∈ K, ∀ v : Point n, ‖v‖ ≤ c q →
        ContinuousAt (W q) (uniformFlowExp g gi hC hK q v))
    -- the PLATEAU leg (uniform, `r² < a²`):
    (hplat : ∀ τ : ℝ, 0 < τ → ∀ q ∈ K, ∀ v : Point n, rncRadialSq v < a ^ 2 →
        S q ∈ nhds (uniformFlowExp g gi hC hK q v) →
        |heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b W)) τ
            (uniformFlowExp g gi hC hK q v) q|
          ≤ (P₀a + P₁a * τ) * (((rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ) ^ 2
                + rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ + 1)
              * gaussDdim (4 / 3 * τ) (uniformFlowExp g gi hC hK q v - q)))
    -- the ANNULUS leg (uniform, `a² ≤ r² ≤ b²`):
    (hann : ∀ τ : ℝ, 0 < τ → ∀ q ∈ K, ∀ v : Point n,
        a ^ 2 ≤ rncRadialSq v → rncRadialSq v ≤ b ^ 2 →
        S q ∈ nhds (uniformFlowExp g gi hC hK q v) →
        |heatOp g gi (gatedKernel K S (globalCutoffParametrixWitnessN 1 Θ u a b W)) τ
            (uniformFlowExp g gi hC hK q v) q|
          ≤ (P₀b + P₁b * τ) * (((rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ) ^ 2
                + rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ + 1)
              * gaussDdim (4 / 3 * τ) (uniformFlowExp g gi hC hK q v - q))) :
    QIQTH.HgateAffineRepair.AffineGateBound g gi K S
      (globalCutoffParametrixWitnessN 1 Θ u a b W) (max P₀a P₀b) (max P₁a P₁b) := by
  have hb0 : (0 : ℝ) < b := lt_trans ha hab
  have hab2 : a ^ 2 ≤ b ^ 2 := by nlinarith [ha, hab]
  intro τ hτ q hq p hp
  -- (C1) parametrize `p = φ_q v`, `‖v‖ ≤ c q`.
  obtain ⟨v, hvc, hpv⟩ := expPoint_of_mem_closure g gi hC hK (hSclos q hq) hp
  subst hpv
  -- the width-`4/3` envelope (nonnegative) at the displacement `z := φ_q v − q`.
  have hx : 0 ≤ rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ :=
    div_nonneg (rncRadialSq_nonneg _) hτ.le
  have hpoly : 0 ≤ (rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ) ^ 2
      + rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ + 1 :=
    add_nonneg (add_nonneg (sq_nonneg _) hx) zero_le_one
  have hinner0 : 0 ≤ ((rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ) ^ 2
        + rncRadialSq (uniformFlowExp g gi hC hK q v - q) / τ + 1)
      * gaussDdim (4 / 3 * τ) (uniformFlowExp g gi hC hK q v - q) :=
    mul_nonneg hpoly (gaussDdim_nonneg _ _)
  -- the two legs' coefficient pairs ≤ the maxed pair.
  have hc1a : P₀a + P₁a * τ ≤ max P₀a P₀b + max P₁a P₁b * τ :=
    add_le_add (le_max_left _ _) (mul_le_mul_of_nonneg_right (le_max_left _ _) hτ.le)
  have hc1b : P₀b + P₁b * τ ≤ max P₀a P₀b + max P₁a P₁b * τ :=
    add_le_add (le_max_right _ _) (mul_le_mul_of_nonneg_right (le_max_right _ _) hτ.le)
  -- gate-neighbourhood discharge for the interior regions (`r² ≤ b²`).
  have hnhds_of : ∀ w : Point n, rncRadialSq w ≤ b ^ 2 →
      S q ∈ nhds (uniformFlowExp g gi hC hK q w) := by
    intro w hw
    have hrb : rncRadial w ≤ b := by
      have hdef : rncRadial w = Real.sqrt (rncRadialSq w) := rfl
      rw [hdef]
      calc Real.sqrt (rncRadialSq w) ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt hw
        _ = b := Real.sqrt_sq hb0.le
    have hwc : ‖w‖ < c q := lt_of_le_of_lt (le_trans (norm_le_rncRadial w) hrb) (hcb q hq)
    exact (hSopen q hq).mem_nhds (hSmem q hq w hwc)
  -- three-way dispatch on `rncRadialSq v`.
  by_cases h1 : rncRadialSq v < a ^ 2
  · -- PLATEAU.
    have hnhds := hnhds_of v (le_of_lt (lt_of_lt_of_le h1 hab2))
    exact le_trans (hplat τ hτ q hq v h1 hnhds) (mul_le_mul_of_nonneg_right hc1a hinner0)
  · push_neg at h1
    by_cases h2 : rncRadialSq v ≤ b ^ 2
    · -- ANNULUS.
      have hnhds := hnhds_of v h2
      exact le_trans (hann τ hτ q hq v h1 h2 hnhds) (mul_le_mul_of_nonneg_right hc1b hinner0)
    · push_neg at h2
      -- EXTERIOR: the gated heatOp vanishes.
      have hWv : W q (uniformFlowExp g gi hC hK q v) = v := hWpt q hq v hvc
      have hb2W : b ^ 2 < rncRadialSq (W q (uniformFlowExp g gi hC hK q v)) := by
        rw [hWv]; exact h2
      have hzero := gatedHeatOp_eq_zero_exterior g gi K S Θ u a b W τ
        (uniformFlowExp g gi hC hK q v) q ha hab (hWcont q hq v hvc) hb2W
      rw [hzero, abs_zero]
      exact mul_nonneg (add_nonneg (le_trans hP₀a (le_max_left _ _))
        (mul_nonneg (le_trans hP₁a (le_max_left _ _)) hτ.le)) hinner0

end QIQTH.AffineGateCapstone

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.AffineGateCapstone.expPoint_of_mem_closure
#print axioms QIQTH.AffineGateCapstone.gatedHeatOp_eq_zero_exterior
#print axioms QIQTH.AffineGateCapstone.affineGateBound_of_legs
