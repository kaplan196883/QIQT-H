/-
  MixedSliverGatedEstimates — the GLOBAL ∀z GATING LAYER for the five RNC chart-surface estimates.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6` and proves nothing new about `R/6`.  It is the pure
  BOOKKEEPING / redefinition layer of the a₁=R/6 mixed-sliver campaign's chart-surface residue (J4-797):
  it turns the PER-POINT BALL forms of the five RNC chart-surface estimates (`hco`/`hVdisp`/`hJ3i`/
  `hJ3j`/`hJ3Q`), each of which holds only on a gate set `G` (the injectivity ball `K ∩ ball 0 r`, off
  which the `.choose`-built inverse chart is junk), into the GLOBAL `∀ z : Point n` forms that
  `MixedSliverXUniform.witness_sliver2_xuniform_mixed` literally carries.

  ── THE IDEA (per J4-797).  Redefine `V`/`Pi`/`Pj`/`Q` as GATED versions:
        `V  := fun z => if z ∈ G then V z  else −z`        (off-gate: the trivial `−id` displacement)
        `Pi := fun z => if z ∈ G then Pi z else eᵢ`        (off-gate: the trivial identity jet)
        `Pj := fun z => if z ∈ G then Pj z else eⱼ`
        `Q  := fun z => if z ∈ G then Q z  else 0`         (off-gate: the trivial zero 2-jet)
  Off the gate the placeholder values satisfy each of the five estimates TRIVIALLY:
    • `hco`   : `V z = −z`, `rncRadialSq (−z) = rncRadialSq z ≥ (1/2)·rncRadialSq z`  (nonneg).
    • `hVdisp`: `V z + z = 0`, `‖0‖ = 0 ≤ C_W·‖z‖²`.
    • `hJ3i`  : `Pi z − eᵢ = 0`, `‖0‖ = 0 ≤ C_P·‖z‖`.
    • `hJ3j`  : symmetric.
    • `hJ3Q`  : `Q z = 0`, `‖0‖ = 0 ≤ C_Q`.
  On the gate the gated value equals the raw chart value, so the estimate is inherited from the ball form.
  Hence the FIVE global `∀ z` estimates hold for the gated maps — the exact shapes the mixed sliver needs.

  ── WHAT LANDS (all abstract; no `sorry`, no new axioms, no `:= True`; NOT `a₁ = R/6`).
    * `gateDisp`/`gateJet`/`gateQ` — the three gate combinators (`V`-style, `P`-style, `Q`-style).
    * `gateDisp_hco_global` — the global `hco` for the gated displacement.
    * `gateDisp_hVdisp_global` — the global `hVdisp` for the gated displacement.
    * `gateJet_hJ3_global` — the global first-jet gap for a gated jet (serves both `hJ3i` and `hJ3j`).
    * `gateQ_bound_global` — the global second-jet bound for the gated 2-jet.
    * `rncRadialSq_neg` — the elementary `rncRadialSq (−z) = rncRadialSq z` used off-gate.

  Every hypothesis is satisfiable and non-vacuous (`G = univ` recovers the raw estimates; `G = ∅`
  recovers the trivial placeholders; `C_W = C_P = C_Q = 0` still satisfies the off-gate legs), and none
  equals the conclusion.  This is the "bookkeeping/redefinition task" J4-797 named as the global-gating
  wall — discharged in general form.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.SliverAssembly

open MeasureTheory Finset Classical
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.HeatResidualBound
open scoped BigOperators

namespace QIQTH.MixedSliverGatedEstimates

variable {n : ℕ}

/-- **Elementary — `rncRadialSq` is even.** `rncRadialSq (−z) = rncRadialSq z`, since each coordinate is
    squared.  Used to discharge the off-gate `hco` leg where the placeholder is `V z = −z`. -/
theorem rncRadialSq_neg (z : Point n) : rncRadialSq (-z) = rncRadialSq z := by
  simp only [rncRadialSq]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Pi.neg_apply, neg_sq]

/-! ############################################################################
    ### The three gate combinators.
    ############################################################################ -/

/-- The GATED displacement map: the raw chart displacement `V` on the gate set `G`, the trivial `−id`
    placeholder off it.  Off-gate `−z` satisfies both `hco` and `hVdisp` for free. -/
noncomputable def gateDisp (G : Set (Point n)) (V : Point n → Point n) : Point n → Point n :=
  fun z => if z ∈ G then V z else -z

/-- The GATED first jet: the raw chart jet `P` on `G`, the trivial unit-vector placeholder `eᵢ` off it.
    Off-gate `eᵢ` satisfies the first-jet gap `‖· − eᵢ‖ ≤ C_P·‖z‖` for free (the gap is `0`). -/
noncomputable def gateJet (G : Set (Point n)) (P : Point n → Point n) (i : Fin n) :
    Point n → Point n :=
  fun z => if z ∈ G then P z else unitVec i

/-- The GATED second jet: the raw chart 2-jet `Q` on `G`, the trivial zero placeholder off it.
    Off-gate `0` satisfies the bound `‖·‖ ≤ C_Q` for free. -/
noncomputable def gateQ (G : Set (Point n)) (Q : Point n → Point n) : Point n → Point n :=
  fun z => if z ∈ G then Q z else 0

/-! ############################################################################
    ### The five GLOBAL estimates for the gated maps.
    ############################################################################ -/

/-- **★ GLOBAL `hco` — `gateDisp_hco_global`.**  If the raw near-isometry coercivity holds ON the gate,
    then the gated displacement satisfies it GLOBALLY: `∀ z, (1/2)·rncRadialSq z ≤ rncRadialSq (V_gated z)`.
    On-gate: inherited.  Off-gate: `V_gated z = −z`, `rncRadialSq (−z) = rncRadialSq z ≥ (1/2)·rncRadialSq z`. -/
theorem gateDisp_hco_global (G : Set (Point n)) (V : Point n → Point n)
    (hco_on : ∀ z ∈ G, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (V z)) :
    ∀ z : Point n, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (gateDisp G V z) := by
  intro z
  unfold gateDisp
  by_cases hz : z ∈ G
  · rw [if_pos hz]; exact hco_on z hz
  · rw [if_neg hz, rncRadialSq_neg]
    have h := rncRadialSq_nonneg z; linarith

/-- **★ GLOBAL `hVdisp` — `gateDisp_hVdisp_global`.**  If the raw quadratic displacement bound holds ON
    the gate, then the gated displacement satisfies it GLOBALLY: `∀ z, ‖V_gated z + z‖ ≤ C_W·‖z‖²`.
    On-gate: inherited.  Off-gate: `V_gated z + z = −z + z = 0`, `‖0‖ = 0 ≤ C_W·‖z‖²` (`0 ≤ C_W`). -/
theorem gateDisp_hVdisp_global (G : Set (Point n)) (V : Point n → Point n) (C_W : ℝ)
    (hC_W : 0 ≤ C_W)
    (hVdisp_on : ∀ z ∈ G, ‖V z + z‖ ≤ C_W * ‖z‖ ^ 2) :
    ∀ z : Point n, ‖gateDisp G V z + z‖ ≤ C_W * ‖z‖ ^ 2 := by
  intro z
  unfold gateDisp
  by_cases hz : z ∈ G
  · rw [if_pos hz]; exact hVdisp_on z hz
  · rw [if_neg hz, neg_add_cancel, norm_zero]; positivity

/-- **★ GLOBAL first-jet gap — `gateJet_hJ3_global`.**  If the raw first-jet gap holds ON the gate, then
    the gated jet satisfies it GLOBALLY: `∀ z, ‖P_gated z − eᵢ‖ ≤ C_P·‖z‖`.  Serves BOTH `hJ3i` (at `i`)
    and `hJ3j` (at `j`).  On-gate: inherited.  Off-gate: `P_gated z − eᵢ = eᵢ − eᵢ = 0`. -/
theorem gateJet_hJ3_global (G : Set (Point n)) (P : Point n → Point n) (i : Fin n) (C_P : ℝ)
    (hC_P : 0 ≤ C_P)
    (hJ3_on : ∀ z ∈ G, ‖P z - unitVec i‖ ≤ C_P * ‖z‖) :
    ∀ z : Point n, ‖gateJet G P i z - unitVec i‖ ≤ C_P * ‖z‖ := by
  intro z
  unfold gateJet
  by_cases hz : z ∈ G
  · rw [if_pos hz]; exact hJ3_on z hz
  · rw [if_neg hz, sub_self, norm_zero]; positivity

/-- **★ GLOBAL second-jet bound — `gateQ_bound_global`.**  If the raw second-jet bound holds ON the gate,
    then the gated 2-jet satisfies it GLOBALLY: `∀ z, ‖Q_gated z‖ ≤ C_Q`.  On-gate: inherited.  Off-gate:
    `Q_gated z = 0`, `‖0‖ = 0 ≤ C_Q` (`0 ≤ C_Q`). -/
theorem gateQ_bound_global (G : Set (Point n)) (Q : Point n → Point n) (C_Q : ℝ)
    (hC_Q : 0 ≤ C_Q)
    (hJ3Q_on : ∀ z ∈ G, ‖Q z‖ ≤ C_Q) :
    ∀ z : Point n, ‖gateQ G Q z‖ ≤ C_Q := by
  intro z
  unfold gateQ
  by_cases hz : z ∈ G
  · rw [if_pos hz]; exact hJ3Q_on z hz
  · rw [if_neg hz, norm_zero]; exact hC_Q

/-! ############################################################################
    ### Packaged: all five global estimates at once (the sliver's geometric carry).
    ############################################################################ -/

/-- **★★ THE PACKAGED GLOBAL GEOMETRIC CARRY — `gated_five_estimates_global`.**  Given the five RNC
    chart-surface estimates as PER-POINT-ON-GATE hypotheses (the ball forms of J4-796/797/798), the gated
    maps `gateDisp G V`, `gateJet G Pi i`, `gateJet G Pj j`, `gateQ G Q` satisfy ALL FIVE of the mixed
    sliver's global `∀ z` geometric carries `hco`/`hVdisp`/`hJ3i`/`hJ3j`/`hJ3Q` simultaneously.  This is
    the exact bundle `MixedSliverXUniform.witness_sliver2_xuniform_mixed` consumes for its geometry inputs,
    now supplied globally from ball-local data.  ⚠ NOT `a₁ = R/6`. -/
theorem gated_five_estimates_global (G : Set (Point n)) (V Pi Pj Q : Point n → Point n)
    (i j : Fin n) (C_W C_P C_Q : ℝ) (hC_W : 0 ≤ C_W) (hC_P : 0 ≤ C_P) (hC_Q : 0 ≤ C_Q)
    (hco_on : ∀ z ∈ G, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (V z))
    (hVdisp_on : ∀ z ∈ G, ‖V z + z‖ ≤ C_W * ‖z‖ ^ 2)
    (hJ3i_on : ∀ z ∈ G, ‖Pi z - unitVec i‖ ≤ C_P * ‖z‖)
    (hJ3j_on : ∀ z ∈ G, ‖Pj z - unitVec j‖ ≤ C_P * ‖z‖)
    (hJ3Q_on : ∀ z ∈ G, ‖Q z‖ ≤ C_Q) :
    (∀ z : Point n, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (gateDisp G V z))
    ∧ (∀ z : Point n, ‖gateDisp G V z + z‖ ≤ C_W * ‖z‖ ^ 2)
    ∧ (∀ z : Point n, ‖gateJet G Pi i z - unitVec i‖ ≤ C_P * ‖z‖)
    ∧ (∀ z : Point n, ‖gateJet G Pj j z - unitVec j‖ ≤ C_P * ‖z‖)
    ∧ (∀ z : Point n, ‖gateQ G Q z‖ ≤ C_Q) :=
  ⟨gateDisp_hco_global G V hco_on,
   gateDisp_hVdisp_global G V C_W hC_W hVdisp_on,
   gateJet_hJ3_global G Pi i C_P hC_P hJ3i_on,
   gateJet_hJ3_global G Pj j C_P hC_P hJ3j_on,
   gateQ_bound_global G Q C_Q hC_Q hJ3Q_on⟩

end QIQTH.MixedSliverGatedEstimates

/-! ## Axiom check — `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.MixedSliverGatedEstimates
#print axioms gated_five_estimates_global
end AxiomChecks
