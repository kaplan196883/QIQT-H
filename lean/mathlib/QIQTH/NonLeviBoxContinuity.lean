/-
  NonLeviBoxContinuity — J4-393: the NON-LEVI BOX CONTINUITY (Sol #16 brick 4) — the box-family FLOOR
  under the three banked strip lifts `JointContinuityAtoms.hHeatCont_of_boxes`,
  `JointContinuityAtoms.hSecCont_of_boxes` and `LapContBoxGlue.hLapCont_of_boxes`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING about `R/6`.  `a₁ = R/6`
  remains CONDITIONAL on the whole `hDuhamel` / convergence-trio + geometric-wiring stack AND on the
  SURVIVING labelled census carries.  This file only reduces the positive-time-compact BOX continuity
  family carried by those three strip lifts (the `Icc (τ₀/2) T ×ˢ closedBall 0 R` shape) to its honest
  lower-level pieces — the banked positive-time Gaussian continuities (`gaussDdim`, its `τ`-derivative,
  the parametrix `τ`-derivative) plus the genuinely-buried witness-slice `∂_τ`/spatial-partial
  continuities carried honestly.  NO `sorry` (header prose excepted), NO new axioms, NO `:= True`, NO
  vacuous / unsatisfiable hypothesis, NONE equal to (or trivially yielding) the conclusion, NO existing
  file edited, nothing committed, nothing wired into `QIQTH.lean` / `AxiomAudit`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE SLOT-ORDER VERDICT (Phase-1, dont-undercredit).

    The banked `HeatOpWitnessContinuity` / `ParametrixPartsContinuity` route proves box continuity of
    `p ↦ heatOp g gi Wit p.1 p.2 0` — i.e. the FIRST spatial slot (`x`) VARYING, the SECOND (`y`)
    FROZEN at `0`.  The three strip lifts here instead need `p ↦ heatOp g gi Wit p.1 0 p.2` — the FIRST
    spatial slot FROZEN at `0`, the SECOND (`y`) VARYING.  Since
      `heatOp g gi K t x y = deriv (fun u => K u x y) t − laplaceBeltrami g gi (fun p => K t p y) x`,
    the two orientations differ in WHERE the Laplacian is evaluated (at the varying `x` in the banked
    route, at the fixed `0` here) — they are DIFFERENT objects, so the banked heatOp box continuity is
    NOT slot-generic and does NOT transport directly.  What IS slot-generic — and what this file uses —
    is (i) the banked SCALAR Gaussian continuities `gaussDdim_continuousOn_pos` /
    `gaussDdim_deriv_t_jointContinuousOn` / `heatParametrix_deriv_jointContinuousOn` (functions of the
    single spatial variable, orientation-blind), and (ii) the STRUCTURAL `heatOp` /
    `laplaceBeltrami` unfold-and-`sub`/`finsetSum` reduction, applied in the CORRECT (`x = 0` frozen,
    `y` varying) orientation.  The banked Gaussian nonvanishing supplier is `VanVleck.vanVleck_pos`
    (with `vanVleck_contDiffAt` for smoothness) — it discharges the `Θ ≠ 0` / `Θ` continuity carries of
    the parametrix-`τ`-derivative box piece.

  ## WHAT LANDS (all DERIVED; NO `sorry`, NO new axioms; NOT a₁ = R/6).

    * `box_subset_pos` — the positive-time box `Icc (τ₀/2) T ×ˢ closedBall 0 R` (`0 < τ₀`) sits inside
      the open positive-time strip `{0 < τ}`.  Pure order.

    * (N1a) `gaussDdim_continuousOn_box` — joint `(τ,z)`-continuity of the `d`-D Gaussian on the box
      (`gaussDdim_continuousOn_pos.mono`); the `τ₀/2` floor kills the `τ → 0` blow-up.
    * (N1b) `gaussDdim_deriv_t_continuousOn_box` — joint continuity of its `τ`-derivative on the box
      (`gaussDdim_deriv_t_jointContinuousOn.mono`).
    * (N1c) `heatParametrix_deriv_t_continuousOn_box` — joint continuity of the parametrix
      `τ`-derivative on the box, carrying `Θ` continuity / nonvanishing (satisfiable via
      `vanVleck_pos`/`vanVleck_contDiffAt`) and each `u_k` continuity
      (`heatParametrix_deriv_jointContinuousOn.mono`).

    * (N3) `laplaceBeltrami_slice_continuousOn_box_of_parts` — the laplaceBeltrami-slice BOX reduction
      in the CORRECT orientation.  Joint continuity of
      `p ↦ laplaceBeltrami g gi (fun x => Wit p.1 x p.2) 0` on the box, from the joint continuity of the
      witness slice's FIRST spatial partials `p ↦ pd (fun x => Wit p.1 x p.2) k 0` and SECOND spatial
      partials `p ↦ pd (fun y => pd (fun x => Wit p.1 x p.2) j y) i 0` (the metric / Christoffel factors
      are evaluated at the FIXED `0`, hence constants).  Route: `laplaceBeltrami` unfold +
      `continuousOn_finsetSum` / `.mul` / `.sub`.  The carried second partials are EXACTLY the
      `witnessSecondXDeriv`-family (their diagonal `i = j` IS the `hSecCont_of_boxes` box member) — a
      genuinely-buried atom carried honestly, NOT the conclusion.

    * (N2) `heatOp_slice_continuousOn_box_of_parts` — the heatOp-slice BOX reduction in the CORRECT
      orientation.  Joint continuity of `p ↦ heatOp g gi Wit p.1 0 p.2` on the box, from the joint
      continuity of the witness `∂_τ` slice `p ↦ deriv (fun u => Wit u 0 p.2) p.1` and the
      laplaceBeltrami slice (=(N3)).  Route: `heatOp` unfold + `ContinuousOn.sub`.  The laplaceBeltrami
      summand is DEFEQ the `LapContBoxGlue.hLapCont_of_boxes` box member — so (N2) rests on (N3) plus
      the single `∂_τ`-slice carry.

    * (CAP-H) `hHeatCont_boxes_of_slice_parts` — the `∀ τ₀ ∈ Ioc 0 T, ∀ R` box family EXACTLY in the
      `JointContinuityAtoms.hHeatCont_of_boxes` carry shape, from the two `∀`-quantified slice-part
      carries, by (N2) at each box.
    * (CAP-L) `hLapCont_boxes_of_partials` — the `∀ τ₀ ∈ Ioc 0 T, ∀ R` box family EXACTLY in the
      `LapContBoxGlue.hLapCont_of_boxes` carry shape, from the `∀`-quantified partial carries, by (N3)
      at each box.

  ── HONEST CARRIES (satisfiable, non-vacuous, NEVER the conclusion).
    * `Θ` continuity / nonvanishing + `u_k` continuity — for (N1c); satisfiable for `Θ = vanVleck g`
      via `VanVleck.vanVleck_pos` (nonvanishing where `det g̃ > 0`) and `vanVleck_contDiffAt`
      (smoothness), and for `u = transportCoeff …` via the banked folded-smoothness route.
    * the witness `∂_τ` slice continuity `p ↦ deriv (fun u => Wit u 0 p.2) p.1` — for (N2)/(CAP-H); a
      genuinely-buried atom (the `τ`-derivative of the gated·cutoff·chart-composed van-Vleck kernel with
      `x = 0` frozen), the honest remaining work of the `∂_τ` leg.
    * the witness first/second spatial-partial continuities — for (N3)/(CAP-L); genuinely-buried atoms
      (the diagonal second partial IS `witnessSecondXDeriv`, the `hSecCont_of_boxes` box member), the
      honest remaining spatial-derivative work.

  ⚠ NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.ParametrixPartsContinuity
import QIQTH.LapContBoxGlue

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatDuhamel
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.TrueHeatKernel QIQTH.LeviSeries QIQTH.HeatResidualBound
open QIQTH.LaplaceBeltrami QIQTH.HeatParametrixAnsatz
open QIQTH.InnerKernelJointMeas QIQTH.ParametrixPartsContinuity
open scoped Topology BigOperators

namespace QIQTH.NonLeviBoxContinuity

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### The positive-time box sits inside the open positive-time strip.
    ############################################################################### -/

/-- **`box_subset_pos`.**  The positive-time-compact box `Icc (τ₀/2) T ×ˢ closedBall 0 R` (for
    `0 < τ₀`) is contained in the open positive-time strip `{q | 0 < q.1}`.  The `τ₀/2` floor is
    strictly positive, so every `q` in the box has `q.1 ≥ τ₀/2 > 0` — no `τ → 0` Gaussian blow-up.
    Pure order.  NOT `a₁ = R/6`. -/
theorem box_subset_pos {τ₀ : ℝ} (hτ₀ : 0 < τ₀) (T R : ℝ) :
    (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)
      ⊆ {q : ℝ × Point n | 0 < q.1} := by
  intro q hq
  have hq1 : τ₀ / 2 ≤ q.1 := hq.1.1
  exact lt_of_lt_of_le (by linarith) hq1

/-! ###############################################################################
    ### (N1) — the scalar Gaussian piece continuities on the box.
    ############################################################################### -/

/-- **★ (N1a) `gaussDdim_continuousOn_box`.**  Joint `(τ,z)`-continuity of the `d`-D heat Gaussian
    `p ↦ gaussDdim p.1 p.2` on the positive-time box `Icc (τ₀/2) T ×ˢ closedBall 0 R` (`0 < τ₀`), by
    `.mono` of the banked strip continuity `gaussDdim_continuousOn_pos` along `box_subset_pos`.  Fully
    proven; no carry.  NOT `a₁ = R/6`. -/
theorem gaussDdim_continuousOn_box {τ₀ : ℝ} (hτ₀ : 0 < τ₀) (T R : ℝ) :
    ContinuousOn (fun p : ℝ × Point n => gaussDdim p.1 p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) :=
  gaussDdim_continuousOn_pos.mono (box_subset_pos hτ₀ T R)

/-- **★ (N1b) `gaussDdim_deriv_t_continuousOn_box`.**  Joint `(τ,z)`-continuity of the Gaussian
    `τ`-derivative `p ↦ deriv (fun s => gaussDdim s p.2) p.1` on the positive-time box, by `.mono` of the
    banked `gaussDdim_deriv_t_jointContinuousOn` along `box_subset_pos`.  Fully proven; no carry.  NOT
    `a₁ = R/6`. -/
theorem gaussDdim_deriv_t_continuousOn_box {τ₀ : ℝ} (hτ₀ : 0 < τ₀) (T R : ℝ) :
    ContinuousOn (fun p : ℝ × Point n => deriv (fun s => gaussDdim s p.2) p.1)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) :=
  gaussDdim_deriv_t_jointContinuousOn.mono (box_subset_pos hτ₀ T R)

/-- **★ (N1c) `heatParametrix_deriv_t_continuousOn_box`.**  Joint `(τ,z)`-continuity of the parametrix
    `τ`-derivative `p ↦ deriv (fun s => heatParametrix N Θ u s p.2) p.1` on the positive-time box, from
    `Θ` continuous / non-vanishing (the `Θ^{−1/2}` factor) and each `u_k` continuous, by `.mono` of the
    banked `heatParametrix_deriv_jointContinuousOn` along `box_subset_pos`.  The carries are genuine
    coefficient-regularity facts, satisfiable for `Θ = vanVleck g` (nonvanishing via `vanVleck_pos`,
    smoothness via `vanVleck_contDiffAt`) and `u = transportCoeff …` — none is the conclusion.  NOT
    `a₁ = R/6`. -/
theorem heatParametrix_deriv_t_continuousOn_box (N : ℕ) (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ)
    (hΘc : Continuous Θ) (hΘne : ∀ w, Θ w ≠ 0) (huc : ∀ k, Continuous (u k))
    {τ₀ : ℝ} (hτ₀ : 0 < τ₀) (T R : ℝ) :
    ContinuousOn (fun p : ℝ × Point n => deriv (fun s => heatParametrix N Θ u s p.2) p.1)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) :=
  (heatParametrix_deriv_jointContinuousOn N Θ u hΘc hΘne huc).mono (box_subset_pos hτ₀ T R)

/-! ###############################################################################
    ### (N3) — the laplaceBeltrami-slice box reduction (correct `x = 0` orientation).
    ############################################################################### -/

/-- **★★ (N3) `laplaceBeltrami_slice_continuousOn_box_of_parts` — THE laplaceBeltrami-SLICE REDUCTION.**
    Joint `(τ,z)`-continuity of the gated van-Vleck laplaceBeltrami slice
    `p ↦ laplaceBeltrami g gi (fun x => vanVleckGatedWitness g gi hChr hK S a b p.1 x p.2) 0` on the
    positive-time box `Icc (τ₀/2) T ×ˢ closedBall 0 R`, from the joint continuity of the witness slice's
      • `hpd1` — FIRST spatial partials `p ↦ pd (fun x => Wit p.1 x p.2) k 0`;
      • `hpd2` — SECOND spatial partials `p ↦ pd (fun y => pd (fun x => Wit p.1 x p.2) j y) i 0`.
    Route: unfold `laplaceBeltrami` (a finite `∑_i ∑_j gi 0 i j·(∂²f − ∑_k Γ 0·∂f)`), whose metric /
    Christoffel factors are evaluated at the FIXED point `0` — hence CONSTANTS in `p` — leaving only the
    partials `p`-dependent; then `continuousOn_finsetSum` / `.mul` / `.sub`.  This is the EXACT (fixed
    `T`) member of the `LapContBoxGlue.hLapCont_of_boxes` box family, in the correct (`x = 0` frozen,
    `y = p.2` varying) orientation.  The carried second partials `hpd2` are the `witnessSecondXDeriv`
    family (diagonal `i = j` IS the `hSecCont_of_boxes` box member); genuinely-buried atoms carried
    honestly — none is the conclusion.  NOT `a₁ = R/6`. -/
theorem laplaceBeltrami_slice_continuousOn_box_of_parts
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    {τ₀ : ℝ} (T R : ℝ)
    (hpd1 : ∀ k, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun x => vanVleckGatedWitness g gi hChr hK S a b p.1 x p.2) k 0)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hpd2 : ∀ i j, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun y => pd (fun x => vanVleckGatedWitness g gi hChr hK S a b p.1 x p.2) j y) i 0)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn
      (fun p : ℝ × Point n =>
        laplaceBeltrami g gi
          (fun x => vanVleckGatedWitness g gi hChr hK S a b p.1 x p.2) 0)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
  have hEq :
      (fun p : ℝ × Point n =>
        laplaceBeltrami g gi
          (fun x => vanVleckGatedWitness g gi hChr hK S a b p.1 x p.2) 0)
      = fun p : ℝ × Point n =>
          ∑ i, ∑ j, gi 0 i j *
            (pd (fun y =>
                  pd (fun x => vanVleckGatedWitness g gi hChr hK S a b p.1 x p.2) j y) i 0
              - ∑ k, christoffel g gi k i j 0
                  * pd (fun x => vanVleckGatedWitness g gi hChr hK S a b p.1 x p.2) k 0) := by
    funext p; simp only [laplaceBeltrami]
  rw [hEq]
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_finsetSum
  intro j _
  refine continuousOn_const.mul ((hpd2 i j).sub ?_)
  apply continuousOn_finsetSum
  intro k _
  exact continuousOn_const.mul (hpd1 k)

/-! ###############################################################################
    ### (N2) — the heatOp-slice box reduction (correct `x = 0` orientation).
    ############################################################################### -/

/-- **★★ (N2) `heatOp_slice_continuousOn_box_of_parts` — THE heatOp-SLICE REDUCTION.**  Joint
    `(τ,z)`-continuity of the gated van-Vleck heat operator
    `p ↦ heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) p.1 0 p.2` on the positive-time box, from
      • `hDeriv` — the witness `∂_τ` slice `p ↦ deriv (fun u => Wit u 0 p.2) p.1`, and
      • `hLap`   — the laplaceBeltrami slice `p ↦ laplaceBeltrami g gi (fun x => Wit p.1 x p.2) 0`
        (=(N3), dischargeable by `laplaceBeltrami_slice_continuousOn_box_of_parts`).
    Route: unfold `heatOp` (definitionally `deriv (∂_τ) − laplaceBeltrami (Δ_x)` in the correct
    `x = 0` orientation), then `ContinuousOn.sub`.  This is the EXACT (fixed `T`) member of the
    `JointContinuityAtoms.hHeatCont_of_boxes` box family.  Both carries are genuine, separable
    continuity facts — neither is the conclusion.  NOT `a₁ = R/6`. -/
theorem heatOp_slice_continuousOn_box_of_parts
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    {τ₀ : ℝ} (T R : ℝ)
    (hDeriv : ContinuousOn
      (fun p : ℝ × Point n =>
        deriv (fun u => vanVleckGatedWitness g gi hChr hK S a b u 0 p.2) p.1)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hLap : ContinuousOn
      (fun p : ℝ × Point n =>
        laplaceBeltrami g gi
          (fun x => vanVleckGatedWitness g gi hChr hK S a b p.1 x p.2) 0)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn
      (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) p.1 0 p.2)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
  have hEq :
      (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) p.1 0 p.2)
      = fun p : ℝ × Point n =>
          deriv (fun u => vanVleckGatedWitness g gi hChr hK S a b u 0 p.2) p.1
            - laplaceBeltrami g gi
                (fun x => vanVleckGatedWitness g gi hChr hK S a b p.1 x p.2) 0 := by
    funext p; simp only [heatOp]
  rw [hEq]
  exact hDeriv.sub hLap

/-! ###############################################################################
    ### (CAP) — the `∀ τ₀ ∈ Ioc 0 T, ∀ R` box families in the strip-lift carry shape.
    ############################################################################### -/

/-- **★★ (CAP-L) `hLapCont_boxes_of_partials`.**  The `∀ τ₀ ∈ Ioc 0 T, ∀ R` laplaceBeltrami-slice box
    family EXACTLY in the shape of the `hboxes` carry consumed by `LapContBoxGlue.hLapCont_of_boxes`,
    obtained from the `∀`-quantified first/second spatial-partial carries by
    `laplaceBeltrami_slice_continuousOn_box_of_parts` at each `(τ₀, R)`.  The carried partials are the
    genuinely-buried witness-slice atoms (the `witnessSecondXDeriv` family); NOT the conclusion.  NOT
    `a₁ = R/6`. -/
theorem hLapCont_boxes_of_partials
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (hpd1 : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ k, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun x => vanVleckGatedWitness g gi hChr hK S a b p.1 x p.2) k 0)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hpd2 : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ i j, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun y => pd (fun x => vanVleckGatedWitness g gi hChr hK S a b p.1 x p.2) j y) i 0)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n =>
          laplaceBeltrami g gi
            (fun x => vanVleckGatedWitness g gi hChr hK S a b p.1 x p.2) 0)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
  intro τ₀ hτ₀ R
  exact laplaceBeltrami_slice_continuousOn_box_of_parts g gi hChr hK S a b T R
    (hpd1 τ₀ hτ₀ R) (hpd2 τ₀ hτ₀ R)

/-- **★★ (CAP-H) `hHeatCont_boxes_of_slice_parts`.**  The `∀ τ₀ ∈ Ioc 0 T, ∀ R` heatOp-slice box family
    EXACTLY in the shape of the `hboxes` carry consumed by `JointContinuityAtoms.hHeatCont_of_boxes`,
    obtained from the `∀`-quantified `∂_τ`-slice carry and the laplaceBeltrami-slice family (itself
    dischargeable by `hLapCont_boxes_of_partials`) via `heatOp_slice_continuousOn_box_of_parts` at each
    `(τ₀, R)`.  The carries are the genuinely-buried witness-slice atoms; NOT the conclusion.  NOT
    `a₁ = R/6`. -/
theorem hHeatCont_boxes_of_slice_parts
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (hDeriv : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ContinuousOn
      (fun p : ℝ × Point n =>
        deriv (fun u => vanVleckGatedWitness g gi hChr hK S a b u 0 p.2) p.1)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hLap : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ContinuousOn
      (fun p : ℝ × Point n =>
        laplaceBeltrami g gi
          (fun x => vanVleckGatedWitness g gi hChr hK S a b p.1 x p.2) 0)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ,
      ContinuousOn
        (fun p : ℝ × Point n =>
          heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) p.1 0 p.2)
        (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R) := by
  intro τ₀ hτ₀ R
  exact heatOp_slice_continuousOn_box_of_parts g gi hChr hK S a b T R
    (hDeriv τ₀ hτ₀ R) (hLap τ₀ hτ₀ R)

/-! ###############################################################################
    ### (STRIP) — feeding the box families into the banked strip lifts.
    ############################################################################### -/

/-- **★ (STRIP-L) `hLapCont_strip_of_partials`.**  The FULL positive-time-strip laplaceBeltrami-slice
    continuity `ContinuousOn … (Ioc 0 T ×ˢ univ)` — the exact `hLapCont_of_boxes` conclusion — from the
    `∀`-quantified spatial-partial carries, by composing `hLapCont_boxes_of_partials` with the banked
    strip lift `LapContBoxGlue.hLapCont_of_boxes` (which glues the box family to the strip).  NOT
    `a₁ = R/6`. -/
theorem hLapCont_strip_of_partials
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (hpd1 : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ k, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun x => vanVleckGatedWitness g gi hChr hK S a b p.1 x p.2) k 0)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hpd2 : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ∀ i j, ContinuousOn
      (fun p : ℝ × Point n =>
        pd (fun y => pd (fun x => vanVleckGatedWitness g gi hChr hK S a b p.1 x p.2) j y) i 0)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn
      (fun p : ℝ × Point n =>
        laplaceBeltrami g gi
          (fun x => vanVleckGatedWitness g gi hChr hK S a b p.1 x p.2) 0)
      (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set (Point n))) :=
  QIQTH.LapContBoxGlue.hLapCont_of_boxes g gi hChr hK S a b T
    (hLapCont_boxes_of_partials g gi hChr hK S a b T hpd1 hpd2)

/-- **★ (STRIP-H) `hHeatCont_strip_of_slice_parts`.**  The FULL positive-time-strip heatOp-slice
    continuity `ContinuousOn … (Ioc 0 T ×ˢ univ)` — the exact `hHeatCont_of_boxes` conclusion — from the
    `∀`-quantified `∂_τ`-slice and laplaceBeltrami-slice carries, by composing
    `hHeatCont_boxes_of_slice_parts` with the banked strip lift
    `JointContinuityAtoms.hHeatCont_of_boxes`.  NOT `a₁ = R/6`. -/
theorem hHeatCont_strip_of_slice_parts
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b T : ℝ)
    (hDeriv : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ContinuousOn
      (fun p : ℝ × Point n =>
        deriv (fun u => vanVleckGatedWitness g gi hChr hK S a b u 0 p.2) p.1)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R))
    (hLap : ∀ τ₀ ∈ Set.Ioc (0 : ℝ) T, ∀ R : ℝ, ContinuousOn
      (fun p : ℝ × Point n =>
        laplaceBeltrami g gi
          (fun x => vanVleckGatedWitness g gi hChr hK S a b p.1 x p.2) 0)
      (Set.Icc (τ₀ / 2) T ×ˢ Metric.closedBall (0 : Point n) R)) :
    ContinuousOn
      (fun p : ℝ × Point n =>
        heatOp g gi (vanVleckGatedWitness g gi hChr hK S a b) p.1 0 p.2)
      (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set (Point n))) :=
  QIQTH.JointContinuityAtoms.hHeatCont_of_boxes g gi hChr hK S a b T
    (hHeatCont_boxes_of_slice_parts g gi hChr hK S a b T hDeriv hLap)

/-! ###############################################################################
    ### Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound).
    ############################################################################### -/

#check @box_subset_pos
#check @gaussDdim_continuousOn_box
#check @gaussDdim_deriv_t_continuousOn_box
#check @heatParametrix_deriv_t_continuousOn_box
#check @laplaceBeltrami_slice_continuousOn_box_of_parts
#check @heatOp_slice_continuousOn_box_of_parts
#check @hLapCont_boxes_of_partials
#check @hHeatCont_boxes_of_slice_parts
#check @hLapCont_strip_of_partials
#check @hHeatCont_strip_of_slice_parts

#print axioms box_subset_pos
#print axioms gaussDdim_continuousOn_box
#print axioms gaussDdim_deriv_t_continuousOn_box
#print axioms heatParametrix_deriv_t_continuousOn_box
#print axioms laplaceBeltrami_slice_continuousOn_box_of_parts
#print axioms heatOp_slice_continuousOn_box_of_parts
#print axioms hLapCont_boxes_of_partials
#print axioms hHeatCont_boxes_of_slice_parts
#print axioms hLapCont_strip_of_partials
#print axioms hHeatCont_strip_of_slice_parts

end QIQTH.NonLeviBoxContinuity
