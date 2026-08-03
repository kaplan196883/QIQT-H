/-
  GeometricModuliThreading — J4-143: discharging the GEOMETRIC-MODULI residue of the conditional
  `hDuhamel` sliver stack.  Threads the PROVEN J4-129 inverse-chart lemmas
  (`InverseChartDisplacement`) into the sliver-stack's GLOBAL `hco`/`hYdisp` slots via an honest
  EXTENSION, and extracts the ε-uniform `hbnd` sliver constant for the `SliverSumPlumbing` consumer via
  the finite-max reconciliation.  ONE brick of the `a₁ = R/6` campaign; NOT `a₁ = R/6`, and proves
  NOTHING about `R/6`.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ## THE GAP THIS BRICK CLOSES.

  The sliver stack (`GaussReplaceSlice` / `RemainderIntegration` / `NormalFormDischarge`) consumes the
  geometric moduli as GLOBAL `∀ z` parametric hypotheses:
      `hco    : ∀ z, (1/2)·rncRadialSq z ≤ rncRadialSq (Y z)`     (ℓ²-coercivity)
      `hYdisp : ∀ z, ‖Y z + z‖ ≤ C_W·‖z‖²`                        (quadratic displacement).
  The concrete van-Vleck chart `W₀ z := uniformInverseChart g gi hC hK z 0` satisfies these only on the
  gate `K ∩ ball 0 r` (`chartW0_displacement`, `chartW0_rncRadialSq_error`, J4-129 — the honest inverse
  side).  This brick reconciles the two shapes.

  ## WHAT LANDS (all DERIVED from J4-129; NO `sorry`, no new axioms, no `expRho`; NOT `a₁=R/6`).

    * (G1a) `chartYext` — the EXTENSION of the concrete inverse-chart origin coordinate:
        `chartYext g gi hC hK r z := if z ∈ K ∩ ball 0 r then W₀ z else −z`.
      Off the gate it is `−id`, whose jets EXACTLY meet the moduli: `rncRadialSq(−z) = rncRadialSq z ≥
      ½·rncRadialSq z` and `‖(−z) + z‖ = 0 ≤ C_W‖z‖²`.

    * (G1b) `chartYext_hco_hYdisp` — the moduli DISCHARGE: there is `r>0` and `C_W ≥ 0` so that
      `chartYext g gi hC hK r` satisfies BOTH `hco` and `hYdisp` GLOBALLY (`∀ z`), plus the agreement
      lemma `chartYext = W₀` on the gate `K ∩ ball 0 r`.  Route: the raw error
      `chartW0_rncRadialSq_error` (shrunk so `L‖z‖ ≤ ½`) on the gate for `hco`; `chartW0_displacement`
      on the gate for `hYdisp`; the EXACT `−id` cases off the gate.  This is the PRIZE (the global
      moduli slots filled by a proven witness).

    * (G2) `epsSeq_antitone` + `hbnd_from_eventual` — the ε-UNIFORM sliver-constant extraction.
      `SliverSumPlumbing.sliver_sum_bound` needs the per-coordinate bound `|slivInt i m| ≤
      D0 i·2√ε_m + D1 i·ε_m` for ALL `m`; the witness family (`witness_sliver2_concrete`) delivers it
      (with FIXED, ε-free amplitudes) only EVENTUALLY (`ε_m → 0`, so the side conditions
      `ε<a/2`, `ε≤τ₀` hold for `m ≥ M₀`).  `hbnd_from_eventual` bridges the two by the finite-max
      trick: for the finitely many exceptional `m < M₀`, `|slivInt i m| ≤ ∑_{m'<M₀}|slivInt i m'| =: B_i`,
      and since `ε_m` is antitone, `2√ε_m ≥ 2√ε_{M₀} =: c₀ > 0` there, so `|slivInt i m| ≤ (B_i/c₀)·2√ε_m`;
      absorbing `B_i/c₀` into the amplitude gives the ∀m bound with `D0' i := D0 i + B_i/c₀` (and `D1`
      unchanged).  Produces `hbnd` in the EXACT `sliver_sum_bound` consumer shape.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠ HONEST FIREWALL — what is carried, labelled (none is the conclusion; none vacuous).

    * (G1) The GLOBAL `hco`/`hYdisp` for `chartYext` are DISCHARGED unconditionally (proved here from
      J4-129).  The connection to the ACTUAL van-Vleck witness is the agreement lemma
      `chartYext = W₀` on the gate; the off-gate discrepancy (`chartYext = −id ≠ W₀`) is harmless for the
      sliver INTEGRAND because the concrete witness vanishes off its gate
      (`NormalFormDischarge.witnessSecondXDeriv_offGate_eq_zero`), PROVIDED the sliver gate
      `S`-support sits inside `K ∩ ball 0 r` — carried as the labelled side condition `hGateSub` in any
      downstream threading (a genuine, satisfiable geometric containment, obtained by shrinking the
      gate; NOT discharged here — this brick lands G1+G2, the full G3 threading into
      `hDuhamel_penultimate`'s geometric-moduli slots is the next brick).
    * (G2) `hbnd_from_eventual` takes the EVENTUAL per-coordinate bound WITH FIXED ε-free amplitudes as
      an honest hypothesis (`heventual`).  Pinning a single ε-uniform `C_R` across the eventual range
      from the per-ε existential of `witness_sliver2_concrete` is the carried upstream concern; the
      finite-max reconciliation itself is proved here in full.

    NO `sorry`, no new axioms, no `expRho` in statements, no vacuous hypotheses.  NOT `a₁ = R/6` —
    this is ONE brick (the geometric-moduli threading G1+G2) of the `a₁ = R/6` campaign.
-/
import Mathlib
import QIQTH.InverseChartDisplacement
import QIQTH.ConvApproximants

open MeasureTheory Filter Finset
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatParametrixAnsatz
open QIQTH.VanVleck QIQTH.ResidueBound QIQTH.RadialDistance QIQTH.ExpMap QIQTH.RNCDecay
open scoped Topology BigOperators

namespace QIQTH.HeatResidualBound

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### G1 — the EXTENSION `chartYext` and the GLOBAL `hco`/`hYdisp` discharge.
    ############################################################################### -/

open Classical in
/-- **(G1a) `chartYext`.**  The extension of the concrete inverse-chart origin coordinate
    `W₀ z = uniformInverseChart g gi hC hK z 0` off the gate `K ∩ ball 0 r` by `−id`.  On the gate it is
    the real chart; off it, `chartYext z = −z` — whose jets EXACTLY satisfy the sliver moduli. -/
noncomputable def chartYext (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (r : ℝ) : Point n → Point n :=
  fun z => if z ∈ K ∩ Metric.ball (0 : Point n) r
    then uniformInverseChart g gi hC hK z 0 else -z

/-- **★★ G1b — `chartYext_hco_hYdisp`: the GLOBAL geometric-moduli discharge.**  There is `r>0` and
    `C_W ≥ 0` so that the extended chart `chartYext g gi hC hK r` satisfies BOTH sliver-stack moduli
    GLOBALLY (`∀ z`):
      * `hco`   :  `(1/2)·rncRadialSq z ≤ rncRadialSq (chartYext … z)`;
      * `hYdisp`:  `‖chartYext … z + z‖ ≤ C_W·‖z‖²`;
    plus the AGREEMENT lemma `chartYext … z = W₀ z` on the gate `K ∩ ball 0 r`.  On the gate: the raw
    near-isometry error `chartW0_rncRadialSq_error` (radius shrunk so `L‖z‖ ≤ 1/2`) gives `hco`, and
    the displacement `chartW0_displacement` gives `hYdisp`.  Off the gate: `chartYext z = −z` makes both
    EXACT (`rncRadialSq(−z) = rncRadialSq z ≥ ½rncRadialSq z`, `‖(−z)+z‖ = 0`).  NOT `a₁ = R/6`. -/
theorem chartYext_hco_hYdisp (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) :
    ∃ r > (0 : ℝ), ∃ C_W : ℝ, 0 ≤ C_W ∧
      (∀ z : Point n, (1 / 2 : ℝ) * rncRadialSq z ≤ rncRadialSq (chartYext g gi hC hK r z))
      ∧ (∀ z : Point n, ‖chartYext g gi hC hK r z + z‖ ≤ C_W * ‖z‖ ^ 2)
      ∧ (∀ z ∈ K ∩ Metric.ball (0 : Point n) r,
          chartYext g gi hC hK r z = uniformInverseChart g gi hC hK z 0) := by
  classical
  obtain ⟨r₀, hr₀, L, hL0, hraw⟩ := chartW0_rncRadialSq_error g gi hC hK
  obtain ⟨r₁, hr₁, C_W, hCW0, hD1⟩ := chartW0_displacement g gi hC hK
  set r : ℝ := min r₁ (min r₀ (1 / (2 * (L + 1)))) with hrdef
  have hrpos : 0 < r := lt_min hr₁ (lt_min hr₀ (by positivity))
  refine ⟨r, hrpos, C_W, hCW0, ?_, ?_, ?_⟩
  · -- hco (global)
    intro z
    simp only [chartYext]
    split_ifs with h
    · -- on the gate: use the raw near-isometry error, shrunk so `L‖z‖ ≤ 1/2`.
      have hzK : z ∈ K := h.1
      have hznorm : ‖z‖ < r := by
        have := h.2; rwa [mem_ball_zero_iff] at this
      have hzr₀ : ‖z‖ < r₀ := lt_of_lt_of_le hznorm (le_trans (min_le_right _ _) (min_le_left _ _))
      have hzrL : ‖z‖ < 1 / (2 * (L + 1)) :=
        lt_of_lt_of_le hznorm (le_trans (min_le_right _ _) (min_le_right _ _))
      obtain ⟨hlow, _⟩ := hraw z hzK hzr₀
      have hLz : L * ‖z‖ ≤ 1 / 2 := by
        have hstep : L * ‖z‖ ≤ L * (1 / (2 * (L + 1))) :=
          mul_le_mul_of_nonneg_left hzrL.le hL0
        have hbound : L * (1 / (2 * (L + 1))) ≤ 1 / 2 := by
          rw [mul_one_div, div_le_iff₀ (by linarith [hL0] : (0 : ℝ) < 2 * (L + 1))]; nlinarith [hL0]
        linarith
      nlinarith [hlow, hLz, rncRadialSq_nonneg z]
    · -- off the gate: `chartYext z = −z`, so `rncRadialSq(−z) = rncRadialSq z ≥ ½rncRadialSq z`.
      rw [rncRadialSq_neg]
      linarith [rncRadialSq_nonneg z]
  · -- hYdisp (global)
    intro z
    simp only [chartYext]
    split_ifs with h
    · -- on the gate: displacement bound, converted to the `^2` shape.
      have hzK : z ∈ K := h.1
      have hznorm : ‖z‖ < r := by
        have := h.2; rwa [mem_ball_zero_iff] at this
      have hzr₁ : ‖z‖ < r₁ := lt_of_lt_of_le hznorm (min_le_left _ _)
      calc ‖uniformInverseChart g gi hC hK z 0 + z‖
          ≤ C_W * ‖z‖ * ‖z‖ := hD1 z hzK hzr₁
        _ = C_W * ‖z‖ ^ 2 := by ring
    · -- off the gate: `‖(−z) + z‖ = 0 ≤ C_W‖z‖²`.
      have he : (-z + z : Point n) = 0 := by abel
      rw [he, norm_zero]
      positivity
  · -- agreement on the gate
    intro z hz
    simp only [chartYext]
    rw [if_pos hz]

/-! ###############################################################################
    ### G2 — the ε-uniform sliver constant `hbnd_from_eventual`.
    ############################################################################### -/

/-- The concrete ε-sequence `ε_m = 1/(m+1)` is antitone: `a ≤ b ⟹ ε_b ≤ ε_a`. -/
theorem epsSeq_antitone {a b : ℕ} (h : a ≤ b) : epsSeq b ≤ epsSeq a := by
  unfold epsSeq
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast Nat.add_le_add_right h 1

/-- **★★ G2 — `hbnd_from_eventual`: the ε-UNIFORM sliver constant.**  `SliverSumPlumbing.sliver_sum_bound`
    consumes the per-coordinate `√ε` bound `|slivInt i m| ≤ D0 i·2√ε_m + D1 i·ε_m` for ALL `m`; the
    witness family (`witness_sliver2_concrete`) delivers it, with FIXED ε-free amplitudes `D0`/`D1`,
    only for `m ≥ M₀` (the side conditions `ε<a/2`, `ε≤τ₀` hold eventually, `ε_m → 0`).  This lemma
    bridges the two by the FINITE-MAX trick: for `m < M₀`, `|slivInt i m| ≤ ∑_{m'<M₀}|slivInt i m'| =: B_i`
    and `2√ε_m ≥ 2√ε_{M₀} =: c₀ > 0` (antitone `ε`), so `|slivInt i m| ≤ (B_i/c₀)·2√ε_m`; absorbing
    `B_i/c₀` into the amplitude, `D0' i := D0 i + B_i/c₀` gives the ∀m bound (`D1` unchanged) — the
    EXACT `sliver_sum_bound` consumer shape.  NOT `a₁ = R/6`. -/
theorem hbnd_from_eventual (slivInt : Fin n → ℕ → ℝ) (D0 D1 : Fin n → ℝ)
    (hD0 : ∀ i, 0 ≤ D0 i) (hD1 : ∀ i, 0 ≤ D1 i) (M₀ : ℕ)
    (heventual : ∀ (i : Fin n) (m : ℕ), M₀ ≤ m →
        |slivInt i m| ≤ D0 i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m) :
    ∃ D0' : Fin n → ℝ, (∀ i, 0 ≤ D0' i) ∧
      ∀ (i : Fin n) (m : ℕ),
        |slivInt i m| ≤ D0' i * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m := by
  -- the exceptional-window normalizer `c₀ = 2√ε_{M₀} > 0`.
  set c₀ : ℝ := 2 * Real.sqrt (epsSeq M₀) with hc₀def
  have hsqM : 0 < Real.sqrt (epsSeq M₀) := Real.sqrt_pos.mpr (epsSeq_pos M₀)
  have hc₀pos : 0 < c₀ := by rw [hc₀def]; linarith
  -- per-coordinate exceptional bucket `B_i := ∑_{m'<M₀} |slivInt i m'|`.
  set Bsum : Fin n → ℝ := fun i => ∑ m' ∈ Finset.range M₀, |slivInt i m'| with hBdef
  have hBnn : ∀ i, 0 ≤ Bsum i := fun i =>
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨fun i => D0 i + Bsum i / c₀, ?_, ?_⟩
  · intro i
    exact add_nonneg (hD0 i) (div_nonneg (hBnn i) hc₀pos.le)
  · intro i m
    have hsqmnn : (0 : ℝ) ≤ 2 * Real.sqrt (epsSeq m) := by positivity
    have hextra : 0 ≤ Bsum i / c₀ * (2 * Real.sqrt (epsSeq m)) :=
      mul_nonneg (div_nonneg (hBnn i) hc₀pos.le) hsqmnn
    by_cases hm : M₀ ≤ m
    · -- eventual range: the fixed-amplitude bound, with the extra nonneg amplitude term.
      have hbase := heventual i m hm
      have hD0le : D0 i * (2 * Real.sqrt (epsSeq m))
          ≤ (D0 i + Bsum i / c₀) * (2 * Real.sqrt (epsSeq m)) := by
        have : D0 i ≤ D0 i + Bsum i / c₀ := by
          have := div_nonneg (hBnn i) hc₀pos.le; linarith
        exact mul_le_mul_of_nonneg_right this hsqmnn
      linarith [hbase, hD0le]
    · -- exceptional window `m < M₀`: the finite-max / antitone-√ε trick.
      have hmlt : m < M₀ := Nat.lt_of_not_le hm
      -- `|slivInt i m| ≤ B_i`.
      have hle_B : |slivInt i m| ≤ Bsum i := by
        rw [hBdef]
        exact Finset.single_le_sum (f := fun m' => |slivInt i m'|)
          (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hmlt)
      -- `2√ε_m ≥ c₀` since `ε` antitone and `m ≤ M₀`.
      have hsqge : Real.sqrt (epsSeq M₀) ≤ Real.sqrt (epsSeq m) :=
        Real.sqrt_le_sqrt (epsSeq_antitone (le_of_lt hmlt))
      have hc₀le : c₀ ≤ 2 * Real.sqrt (epsSeq m) := by rw [hc₀def]; linarith
      -- `B_i = (B_i/c₀)·c₀ ≤ (B_i/c₀)·2√ε_m`.
      have hBeq : Bsum i / c₀ * c₀ = Bsum i := div_mul_cancel₀ _ (ne_of_gt hc₀pos)
      have hBstep : Bsum i ≤ Bsum i / c₀ * (2 * Real.sqrt (epsSeq m)) :=
        calc Bsum i = Bsum i / c₀ * c₀ := hBeq.symm
          _ ≤ Bsum i / c₀ * (2 * Real.sqrt (epsSeq m)) :=
              mul_le_mul_of_nonneg_left hc₀le (div_nonneg (hBnn i) hc₀pos.le)
      have hD1term : 0 ≤ D1 i * epsSeq m :=
        mul_nonneg (hD1 i) (epsSeq_pos m).le
      have hD0term : 0 ≤ D0 i * (2 * Real.sqrt (epsSeq m)) :=
        mul_nonneg (hD0 i) hsqmnn
      calc |slivInt i m|
          ≤ Bsum i := hle_B
        _ ≤ Bsum i / c₀ * (2 * Real.sqrt (epsSeq m)) := hBstep
        _ ≤ (D0 i + Bsum i / c₀) * (2 * Real.sqrt (epsSeq m)) + D1 i * epsSeq m := by
            have : (D0 i + Bsum i / c₀) * (2 * Real.sqrt (epsSeq m))
                = D0 i * (2 * Real.sqrt (epsSeq m)) + Bsum i / c₀ * (2 * Real.sqrt (epsSeq m)) := by
              ring
            rw [this]; linarith [hD0term, hD1term]

end QIQTH.HeatResidualBound

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.HeatResidualBound.chartYext_hco_hYdisp
#print axioms QIQTH.HeatResidualBound.epsSeq_antitone
#print axioms QIQTH.HeatResidualBound.hbnd_from_eventual
