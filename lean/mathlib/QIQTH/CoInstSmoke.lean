/-
  CoInstSmoke — J4-617: THE CAPSTONE CO-INSTANTIATION SMOKE TEST (Sol's priority).

  ══════════════════════════════════════════════════════════════════════════════════════════════
  PURPOSE.  The frozen-Gaussian k ≥ 2 program (J4-609→616) built bounds for
  `E_frozen = frozenDefectKernel K r` — the defect of the FROZEN-Gaussian parametrix
  (metric frozen at the base point `q`).  The a₁ capstones consume a DIFFERENT kernel:

    • FLAT capstone `TrueKernelA1.trueKernel_diagonal_a1_eq_R6` — takes a GENERAL binder `E`,
      but PINS it to the transport/van-Vleck parametrix via
      `hE : heatOp g gi H t 0 0 = E t 0 0` and `hHdiag : H t 0 0 = heatParametrixFn N g …`,
      and its `hCorrHigher` slot wants `heatConv H (leviSeries E) t 0 0 = pref·(t²·cRem)` —
      note `F = leviSeries E = −E + (k ≥ 2 tail)` (k = 1 INCLUDED).
    • CURVED capstone `curved_a1_R6_fully_wired_center` — `E` is DEFINITIONALLY
      `heatOp g^κ gi^κ (vanVleckGatedWitness …)` (the transport parametrix defect), with the
      Gaussian dominations (`hAdomHeat`, `hFdomW`) CARRIED as binders.

  ★ THE BRIDGE VERDICT (this file certifies it):
    (V1) the capstone `hCorrHigher` slot is GENERAL-F in SHAPE, so the frozen `O(t²)` API
         `corrHigher_O_t2_restored` produces a SYNTACTICALLY consumable conjunct — landed
         (`smoke_corrHigher_wired`, at the capstone prefactor `pref = (heatKernel1D t 0)^n`);
    (V2) but the capstone's `E` is the TRANSPORT defect, NOT `E_frozen`, so feeding the banked
         frozen bounds into the capstone's OWN `leviSeries E` slot needs the precise
         frozen-vs-transport BRIDGE Prop `FrozenTransportBridge` (the two k ≥ 2 tails differ by
         `O(s)·G_{8s}` on the center column) — stated here, NOT proved (it is the genuine wall);
    (V3) GIVEN the bridge, the ENTIRE frozen consumer chain transfers: `smoke_bridge_verdict`
         (bridge ⟹ bounded-cRem `O(t²)` API for the transport tail) — landed, via the
         generic slice lemma `tail_slice_of_pointwise` (the banked slice proof abstracted over
         the pointwise tail bound);
    (V4) the k = 1 term `−E` of `leviSeries E = −E + tail` is NOT covered by any of it
         (`leviSeries_split` certifies the decomposition; `K1TransportBudget` states the owed
         Prop — the transport-cancellation thread).

  THE SHARED DEPENDENT STRUCTURE.  `FatFrozenPackage` bundles in ONE record: genuinely curved
  `κ < 0`, `n ≥ 2`, the NESTED radii `0 < rS < rK < rdomain` (frozen gate radius STRICTLY inside
  the compact-base radius STRICTLY inside the domain radius — not `rS := r` collapsed), the
  compact base `closedBall 0 rK ∋ 0`, the center gauge `hg0` (the curved capstone's binder,
  satisfied by `curvedRNCMetric_zero` — no `K = {0}` collapse), the nonzero scalar-curvature
  coefficient gate `n(n−1)κ/6 ≠ 0`, the frozen slice constant `C_t` with its J4-616 budget, and
  the non-vacuity witness (the frozen defect is genuinely nonzero at the gate).
  `fatFrozenPackage_inhabited` instantiates ALL fields JOINTLY (single anonymous constructor at
  `κ = −1`, `rS = 1/2 < rK = 1 < rdomain = 2`) — the cheap anti-vacuity test that would have
  caught the J4-582 `{0}`-collapse (independent ∃'s cannot certify joint instantiability).

  ALSO DISCHARGED HERE: the `H(0,0,·) = 0` endpoint hypothesis for the capstone's ACTUAL `H`
  (`gatedWitness_time_zero` — the van-Vleck gated witness vanishes at time 0), so the only
  UNBANKED hypothesis on the capstone's `H` in the corrHigher slot is its Gaussian domination
  `|H(a,0,ζ)| ≤ C_H·G_{2a}` (the hAdom-family pile — CARRIED, labelled, in
  `smoke_corrHigher_wired_vanVleck`; consistent with the curved capstone's own carried
  `hAdomHeat`).

  ⚠ HONEST SCOPE.  `a₁ = R/6` remains CONDITIONAL: flat tower non-vacuous and closed; the
  curved side owes the bridge Prop (V2), the k = 1 thread (V4), the per-q producer re-assembly,
  the fat-K carrier piles, the full capstone co-instantiation, and the prior piles.  This brick
  is the SMOKE TEST: it certifies joint instantiability of all the choices made so far and
  isolates the two precise owed Props.  No axioms, no sorry, no vacuous hypotheses.
-/
import Mathlib
import QIQTH.FrozenK2Sharp
import QIQTH.ConvApproximants
import QIQTH.InnerKernelJointMeas

open Finset Filter Topology MeasureTheory
open scoped Interval
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation
open QIQTH.GaussianWidthTransfer QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCPosDef
open QIQTH.CurvedRNCGaugeBundle QIQTH.FrozenGauss QIQTH.FrozenDefect
open QIQTH.HeatDuhamel QIQTH.LeviSeries QIQTH.TrueHeatKernel QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.AlphaLevi QIQTH.FrozenWire QIQTH.FrozenColumn
open QIQTH.FrozenK2 QIQTH.FrozenK2Sharp
open QIQTH.VanVleck QIQTH.HeatTransportRecursion QIQTH.ParametrixFunction
open QIQTH.HeatParametrixAnsatz

namespace QIQTH.CoInstSmoke

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### 1. The shared dependent structure — ONE record for ALL the choices. -/

/-- **`FatFrozenPackage` — the shared dependent co-instantiation record.**  Every choice of the
    frozen-Gaussian → capstone chain in ONE structure: genuinely curved `κ < 0`, `n ≥ 2`, the
    NESTED radii `0 < rS < rK < rdomain` (Sol's red flag: the gate radius is strictly inside the
    compact-base radius, strictly inside the domain radius — no collapsed `rS := r`), the compact
    base containing the center, the center-only gauge `hg0` (the curved capstone's binder shape),
    the nonzero curvature-coefficient gate, the J4-616 frozen slice budget, and the frozen-defect
    non-vacuity witness.  Joint inhabitation (below) is the smoke test. -/
structure FatFrozenPackage (n : ℕ) : Type where
  /-- the space-form curvature — genuinely curved. -/
  κ : ℝ
  hκ : κ < 0
  /-- dimension gate (`R(0) = n(n−1)κ ≠ 0` needs `n ≥ 2`). -/
  hn : 2 ≤ n
  /-- the frozen-gate radius (the `r` of `frozenDefectKernel κ r`). -/
  rS : ℝ
  /-- the compact-base radius. -/
  rK : ℝ
  /-- the chart/domain radius. -/
  rdomain : ℝ
  hrS : 0 < rS
  hSK : rS < rK
  hKd : rK < rdomain
  /-- the compact base `K := closedBall 0 rK`. -/
  hKcompact : IsCompact (Metric.closedBall (0 : Point n) rK)
  /-- the center is in the base (the curved capstone's `hK0`). -/
  hK0 : (0 : Point n) ∈ Metric.closedBall (0 : Point n) rK
  /-- the center-only value gauge (the curved capstone's `hg0` binder — NOT the collapsing
      neighbourhood frame `hframeK`). -/
  hg0 : ∀ i j : Fin n, curvedRNCMetric κ (0 : Point n) i j = (if i = j then (1 : ℝ) else 0)
  /-- the a₁-coefficient gate: `n(n−1)κ/6 ≠ 0` (the two-jet target is genuinely nonzero). -/
  hRic : ((n : ℝ) * ((n : ℝ) - 1) * κ) / 6 ≠ 0
  /-- the J4-616 frozen k ≥ 2 tail slice constant. -/
  C_t : ℝ
  hCt : 0 ≤ C_t
  /-- the J4-616 linear slice budget AT THESE gate data (`κ`, `rS`). -/
  hSlice : ∀ (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ), 0 ≤ C_H →
    (∀ (a : ℝ) (ζ : Point n), 0 < a →
      |H a 0 ζ| ≤ C_H * gaussDdim (2 * a) ((0 : Point n) - ζ)) →
    ∀ (t s : ℝ), 0 < s → s < t → s ≤ 1 →
      ‖∫ ζ, H (t - s) 0 ζ
          * (leviSeries (frozenDefectKernel κ rS) s ζ 0 + frozenDefectKernel κ rS s ζ 0)‖
        ≤ (C_H * C_t) * (s * gaussDdim (8 * t) (0 : Point n))
  /-- non-vacuity: the frozen defect is genuinely nonzero at the gate, ALL `τ ∈ (0,1]`. -/
  hWitness : ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
    ∃ p : Point n, frozenDefectKernel κ rS τ p 0 ≠ 0

/-- **★ `fatFrozenPackage_inhabited` — THE SMOKE TEST PROPER.**  ALL fields of the record are
    JOINTLY instantiated at genuinely curved data: `κ = −1 < 0`, nested radii
    `0 < 1/2 < 1 < 2`, the compact ball base with `0 ∈ K`, the center gauge from
    `curvedRNCMetric_zero`, the nonzero coefficient `n(n−1)(−1)/6 ≠ 0` (`n ≥ 2`), the banked
    J4-616 slice budget at exactly these `(κ, rS)`, and the banked frozen-defect non-vacuity
    witness at exactly these `(κ, rS)` — ONE anonymous constructor, NOT independent ∃'s.
    This is the anti-vacuity gate the J4-582 `{0}`-collapse taught (an antecedent pile is only
    as good as its joint inhabitation).  NOT `a₁ = R/6`. -/
theorem fatFrozenPackage_inhabited (n : ℕ) (hn : 2 ≤ n) :
    Nonempty (FatFrozenPackage n) := by
  obtain ⟨C_t, hCt, hslice⟩ :=
    frozenK2_tail_slice_O_s (n := n) (-1) (1 / 2) (by norm_num) (by norm_num)
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  refine ⟨⟨-1, by norm_num, hn, 1 / 2, 1, 2, by norm_num, by norm_num, by norm_num,
    isCompact_closedBall _ _, Metric.mem_closedBall_self (by norm_num),
    fun i j => curvedRNCMetric_zero (-1) i j, ?_, C_t, hCt, hslice,
    fun τ hτ hτ1 =>
      frozenColumn_witness_ne_zero (-1) (1 / 2) (by norm_num) hn τ hτ hτ1⟩⟩
  have hpos : 0 < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
  have hneg : ((n : ℝ) * ((n : ℝ) - 1) * (-1)) / 6 < 0 := by nlinarith
  exact ne_of_lt hneg

/-! ### 2. The capstone's H: endpoint-zero DISCHARGED; the defect it convolves. -/

/-- **`gatedWitness_time_zero` — the capstone's actual `H` satisfies the endpoint-zero
    hypothesis.**  The van-Vleck gated witness vanishes identically at time `0` (`n ≥ 1`): its
    `heatParametrix` core carries the leading `gaussDdim 0 = 0` factor, and both gate branches
    are `0`.  This DISCHARGES the `H(0,0,·) = 0` binder of `corrHigher_O_t2_restored` for the
    capstone's own parametrix — Sol's endpoint-zero red flag, closed for the real `H`. -/
theorem gatedWitness_time_zero (hn : 0 < n)
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (p q : Point n) :
    vanVleckGatedWitness g gi hChr hK S a b 0 p q = 0 := by
  have h0 : ∀ v : Point n,
      heatParametrix 1 (vanVleck g) (transportCoeff (transportOp (vanVleck g) g gi)) 0 v
        = 0 := fun v =>
    QIQTH.InnerKernelJointMeas.heatParametrix_eq_zero_of_nonpos hn 1 _ _ 0 v le_rfl
  simp only [vanVleckGatedWitness, gatedKernel, globalCutoffParametrixWitnessN, h0, mul_zero]
  split_ifs <;> rfl

/-- **`capstoneDefect` — the kernel the capstone chain ACTUALLY convolves.**  The curved capstone
    `curved_a1_R6_fully_wired_center` applies `leviSeries` to
    `heatOp g^κ gi^κ (vanVleckGatedWitness …)` — the TRANSPORT/van-Vleck parametrix defect.
    This is NOT `frozenDefectKernel` (the frozen-Gaussian parametrix defect): the two
    parametrices have different principal terms away from the center (transported amplitude vs
    frozen metric), so their defects and Levi series differ — the precise gap is the bridge
    Prop below.  (At the center base point the two leading Gaussians DO agree:
    `frozenGauss_curvedRNC_center`, banked.) -/
noncomputable def capstoneDefect (κ : ℝ)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y : Point n => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ) :
    ℝ → Point n → Point n → ℝ :=
  heatOp (curvedRNCMetric κ) (curvedRNCInv κ)
    (vanVleckGatedWitness (curvedRNCMetric κ) (curvedRNCInv κ) hChr hK S a b)

/-! ### 3. ★ THE BRIDGE VERDICT — the precise owed Props, and the certified transfer. -/

/-- **★ `FrozenTransportBridge` — THE precise frozen-vs-transport bridge Prop (OWED).**  The
    k ≥ 2 Levi tails of the transport defect `E` and the frozen defect `F` differ by
    `O(s)·G_{8s}` on the center column, `s ∈ (0,1]`.  This is EXACTLY what is needed (and, per
    `smoke_bridge_verdict`, SUFFICIENT) for the banked J4-609→616 frozen bounds to feed the
    capstone's own `leviSeries E` slot.  ⚠ NOT proved here — this is the genuine remaining
    comparison wall (the two parametrices share the center leading Gaussian,
    `frozenGauss_curvedRNC_center`, but their amplitudes differ at first order off-center;
    difficulty: a Levi-iteration comparison argument, comparable in size to J4-612→616). -/
def FrozenTransportBridge (E F : ℝ → Point n → Point n → ℝ) : Prop :=
  ∃ C_B : ℝ, 0 ≤ C_B ∧ ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
    |(leviSeries E s p 0 + E s p 0) - (leviSeries F s p 0 + F s p 0)|
      ≤ C_B * (s * gaussDdim (8 * s) (p - 0))

/-- **`K1TransportBudget` — the k = 1 owed Prop (the transport-cancellation thread).**  The
    capstone's `hCorrHigher` slot takes `F = leviSeries E = −E + (k ≥ 2 tail)`
    (`leviSeries_split`); the frozen program covers the tail only.  The owed k = 1 content:
    the leading Duhamel correction `H ∗ E` is itself `O(t²)` on the diagonal (true for the
    N = 1 transport parametrix, whose defect gains a factor `t` from the transport
    cancellation).  Stated on `E` (the sign of `−E` is immaterial under `|·|`). -/
def K1TransportBudget (H E : ℝ → Point n → Point n → ℝ) : Prop :=
  ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
    |heatConv H E t 0 0| ≤ C₁ * gaussDdim (8 * t) (0 : Point n) * t ^ 2

/-- **`leviSeries_split` — the k = 1 isolation certificate.**  The capstone's correction kernel
    decomposes EXACTLY as `leviSeries E = −E + (leviSeries E + E)`: the first summand is the
    owed k = 1 thread (`K1TransportBudget`), the second is the k ≥ 2 tail covered by the frozen
    program (+ bridge).  Pure algebra — but it PINS the accounting: nothing double-counted,
    nothing dropped. -/
theorem leviSeries_split (E : ℝ → Point n → Point n → ℝ) (s : ℝ) (p q : Point n) :
    leviSeries E s p q = -(E s p q) + (leviSeries E s p q + E s p q) := by ring

/-- **`tail_slice_of_pointwise` — the banked slice budget, GENERIC in the tail.**  The J4-616
    slice proof abstracted over the pointwise bound: ANY center-column kernel `Φ` with
    `|Φ(s,p)| ≤ C_os·s·G_{8s}(p)` on `(0,1]` feeds the linear slice budget
    `(C_H·2ⁿ·C_os)·s·G_{8t}(0)` against every Gaussian-dominated slice kernel `H`.  This is
    what makes the bridge Prop SUFFICIENT: the frozen consumer chain never used anything about
    `E_frozen` beyond this pointwise shape. -/
theorem tail_slice_of_pointwise (Φ : ℝ → Point n → ℝ) (C_os : ℝ) (hCos : 0 ≤ C_os)
    (hΦ : ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
      |Φ s p| ≤ C_os * (s * gaussDdim (8 * s) (p - 0)))
    (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ) (hCH : 0 ≤ C_H)
    (hH : ∀ (a : ℝ) (ζ : Point n), 0 < a →
      |H a 0 ζ| ≤ C_H * gaussDdim (2 * a) ((0 : Point n) - ζ)) :
    ∀ (t s : ℝ), 0 < s → s < t → s ≤ 1 →
      ‖∫ ζ, H (t - s) 0 ζ * Φ s ζ‖
        ≤ (C_H * (2 ^ n * C_os)) * (s * gaussDdim (8 * t) (0 : Point n)) := by
  intro t s hs hst hs1
  have hts : 0 < t - s := by linarith
  have hg_int : Integrable (fun ζ : Point n =>
      (C_H * C_os * s)
        * (gaussDdim (2 * (t - s)) ((0 : Point n) - ζ)
            * gaussDdim (8 * s) (ζ - (0 : Point n)))) volume :=
    (gaussDdim_mul_integrable (2 * (t - s)) (8 * s) (0 : Point n) (0 : Point n)).const_mul _
  have hpt : ∀ ζ : Point n,
      ‖H (t - s) 0 ζ * Φ s ζ‖
        ≤ (C_H * C_os * s)
            * (gaussDdim (2 * (t - s)) ((0 : Point n) - ζ)
                * gaussDdim (8 * s) (ζ - (0 : Point n))) := by
    intro ζ
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hH (t - s) ζ hts
    have h2 := hΦ s ζ hs hs1
    have hGnn : (0 : ℝ) ≤ gaussDdim (2 * (t - s)) ((0 : Point n) - ζ) :=
      QIQTH.ResidueBound.gaussDdim_nonneg _ _
    calc |H (t - s) 0 ζ| * |Φ s ζ|
        ≤ (C_H * gaussDdim (2 * (t - s)) ((0 : Point n) - ζ))
            * (C_os * (s * gaussDdim (8 * s) (ζ - (0 : Point n)))) :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hCH hGnn)
      _ = (C_H * C_os * s)
            * (gaussDdim (2 * (t - s)) ((0 : Point n) - ζ)
                * gaussDdim (8 * s) (ζ - (0 : Point n))) := by ring
  have hwide : gaussDdim (2 * (t - s) + 8 * s) ((0 : Point n) - 0)
      ≤ 2 ^ n * gaussDdim (8 * t) ((0 : Point n) - 0) :=
    gaussDdim_widen_le (2 * (t - s) + 8 * s) (8 * t)
      (by linarith) (by linarith) (by linarith) _
  calc ‖∫ ζ, H (t - s) 0 ζ * Φ s ζ‖
      ≤ ∫ ζ, (C_H * C_os * s)
          * (gaussDdim (2 * (t - s)) ((0 : Point n) - ζ)
              * gaussDdim (8 * s) (ζ - (0 : Point n))) :=
        MeasureTheory.norm_integral_le_of_norm_le hg_int (ae_of_all _ hpt)
    _ = (C_H * C_os * s)
          * ∫ ζ, gaussDdim (2 * (t - s)) ((0 : Point n) - ζ)
              * gaussDdim (8 * s) (ζ - (0 : Point n)) :=
        integral_const_mul _ _
    _ = (C_H * C_os * s) * gaussDdim (2 * (t - s) + 8 * s) ((0 : Point n) - 0) := by
        rw [QIQTH.GaussianConvolution.gaussDdim_conv (2 * (t - s)) (8 * s)
          (by linarith) (by linarith) (0 : Point n) (0 : Point n)]
    _ ≤ (C_H * C_os * s) * (2 ^ n * gaussDdim (8 * t) ((0 : Point n) - 0)) :=
        mul_le_mul_of_nonneg_left hwide (by positivity)
    _ = (C_H * (2 ^ n * C_os)) * (s * gaussDdim (8 * t) (0 : Point n)) := by
        rw [sub_zero]
        ring

/-- **`bridged_tail_pointwise` — bridge ⟹ the TRANSPORT tail has the frozen pointwise shape.**
    Given the bridge Prop, the capstone-defect k ≥ 2 tail obeys the SAME `O(s)·G_{8s}` bound as
    the banked frozen tail (`frozenColumn_tail_O_s`), with constant `C_os + C_B` — a pure
    triangle inequality, no new analysis. -/
theorem bridged_tail_pointwise (P : FatFrozenPackage n) (E : ℝ → Point n → Point n → ℝ)
    (hB : FrozenTransportBridge E (frozenDefectKernel P.κ P.rS)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℝ) (p : Point n), 0 < s → s ≤ 1 →
      |leviSeries E s p 0 + E s p 0| ≤ C * (s * gaussDdim (8 * s) (p - 0)) := by
  obtain ⟨C_B, hCB, hb⟩ := hB
  obtain ⟨C_os, hCos, htail⟩ := frozenColumn_tail_O_s (n := n) P.κ P.rS P.hκ.le P.hrS.le
  refine ⟨C_B + C_os, add_nonneg hCB hCos, fun s p hs hs1 => ?_⟩
  calc |leviSeries E s p 0 + E s p 0|
      = |((leviSeries E s p 0 + E s p 0)
            - (leviSeries (frozenDefectKernel P.κ P.rS) s p 0
                + frozenDefectKernel P.κ P.rS s p 0))
          + (leviSeries (frozenDefectKernel P.κ P.rS) s p 0
              + frozenDefectKernel P.κ P.rS s p 0)| := by congr 1; ring
    _ ≤ |(leviSeries E s p 0 + E s p 0)
            - (leviSeries (frozenDefectKernel P.κ P.rS) s p 0
                + frozenDefectKernel P.κ P.rS s p 0)|
          + |leviSeries (frozenDefectKernel P.κ P.rS) s p 0
              + frozenDefectKernel P.κ P.rS s p 0| := abs_add_le _ _
    _ ≤ C_B * (s * gaussDdim (8 * s) (p - 0))
          + C_os * (s * gaussDdim (8 * s) (p - 0)) :=
        add_le_add (hb s p hs hs1) (htail s p hs hs1)
    _ = (C_B + C_os) * (s * gaussDdim (8 * s) (p - 0)) := by ring

/-- **★★ `smoke_bridge_verdict` — THE CERTIFIED TRANSFER: bridge ⟹ the capstone-shaped bounded
    cRem `O(t²)` API for the TRANSPORT-defect tail.**  Given `FrozenTransportBridge E E_frozen`,
    the whole J4-616 consumer chain re-runs for `F := leviSeries E + E` (the transport k ≥ 2
    tail): the `hCorrHigher` equality shape, the `O(t²)` assembly, and BOUNDED `cRem`.  Combined
    with `leviSeries_split`, the capstone's full `leviSeries E` slot is covered MODULO exactly
    `K1TransportBudget` — so the smoke test's verdict is:
      capstone hCorrHigher  ⟸  FrozenTransportBridge (owed, V2) + K1TransportBudget (owed, V4)
                                 + banked J4-609→616 (this transfer).
    ⚠ NOT `a₁ = R/6`; the bridge and k = 1 Props are genuinely owed. -/
theorem smoke_bridge_verdict (P : FatFrozenPackage n) (E : ℝ → Point n → Point n → ℝ)
    (hB : FrozenTransportBridge E (frozenDefectKernel P.κ P.rS)) :
    ∃ C_t : ℝ, 0 ≤ C_t ∧
      ∀ (H : ℝ → Point n → Point n → ℝ) (C_H : ℝ), 0 ≤ C_H →
        (∀ (a : ℝ) (ζ : Point n), 0 < a →
          |H a 0 ζ| ≤ C_H * gaussDdim (2 * a) ((0 : Point n) - ζ)) →
        (∀ ζ : Point n, H 0 0 ζ = 0) →
        ∀ (pref t : ℝ), 0 < t → t ≤ 1 → pref ≠ 0 →
          (heatConv H (fun σ p q => leviSeries E σ p q + E σ p q) t 0 0
            = pref * (t ^ 2
                * (heatConv H (fun σ p q => leviSeries E σ p q + E σ p q) t 0 0
                    / (pref * t ^ 2))))
          ∧ |heatConv H (fun σ p q => leviSeries E σ p q + E σ p q) t 0 0|
            ≤ (C_H * C_t * gaussDdim (8 * t) (0 : Point n)) * t ^ 2
          ∧ |heatConv H (fun σ p q => leviSeries E σ p q + E σ p q) t 0 0 / (pref * t ^ 2)|
            ≤ (C_H * C_t * gaussDdim (8 * t) (0 : Point n)) / |pref| := by
  obtain ⟨C, hC, hpt⟩ := bridged_tail_pointwise P E hB
  refine ⟨2 ^ n * C, mul_nonneg (by positivity) hC, fun H C_H hCH hH hH0 pref t ht ht1 hpref => ?_⟩
  have hsl := tail_slice_of_pointwise (fun s p => leviSeries E s p 0 + E s p 0) C hC hpt
    H C_H hCH hH
  set Kt : ℝ := C_H * (2 ^ n * C) * gaussDdim (8 * t) (0 : Point n) with hKtdef
  have hKt0 : 0 ≤ Kt := by
    rw [hKtdef]
    exact mul_nonneg (mul_nonneg hCH (mul_nonneg (by positivity) hC))
      (QIQTH.ResidueBound.gaussDdim_nonneg _ _)
  -- the LINEAR slice budget, at EVERY s ∈ Ι 0 t (endpoint s = t via H(0,0,·) = 0)
  have hslice : ∀ s ∈ Ι (0 : ℝ) t,
      ‖∫ ζ, H (t - s) 0 ζ
          * (fun σ p q => leviSeries E σ p q + E σ p q) s ζ 0‖
        ≤ Kt * ((t - s) + s) + 0 * Real.sqrt s := by
    intro s hs
    have hs' : s ∈ Set.Ioc (0 : ℝ) t := by rwa [Set.uIoc_of_le ht.le] at hs
    rcases lt_or_eq_of_le hs'.2 with hst | hseq
    · have hb := hsl t s hs'.1 hst (le_trans hs'.2 ht1)
      calc ‖∫ ζ, H (t - s) 0 ζ * (fun σ p q => leviSeries E σ p q + E σ p q) s ζ 0‖
          = ‖∫ ζ, H (t - s) 0 ζ * (leviSeries E s ζ 0 + E s ζ 0)‖ := rfl
        _ ≤ (C_H * (2 ^ n * C)) * (s * gaussDdim (8 * t) (0 : Point n)) := hb
        _ = Kt * s := by rw [hKtdef]; ring
        _ ≤ Kt * ((t - s) + s) + 0 * Real.sqrt s := by
            have : Kt * s ≤ Kt * ((t - s) + s) :=
              mul_le_mul_of_nonneg_left (by linarith) hKt0
            linarith
    · have hzero : (fun ζ => H (t - s) 0 ζ
          * (fun σ p q => leviSeries E σ p q + E σ p q) s ζ 0) = fun _ => (0 : ℝ) := by
        funext ζ
        rw [hseq, sub_self, hH0 ζ, zero_mul]
      rw [hzero, integral_zero, norm_zero]
      have h1 : Kt * ((t - s) + s) + 0 * Real.sqrt s = Kt * t := by ring
      rw [h1]
      exact mul_nonneg hKt0 ht.le
  obtain ⟨heq, hbd, hrem⟩ := corrHigher_bounded_of_slice_sqrt H
    (fun σ p q => leviSeries E σ p q + E σ p q) pref Kt 0 t ht hpref le_rfl hslice
  refine ⟨heq, ?_, ?_⟩
  · calc |heatConv H (fun σ p q => leviSeries E σ p q + E σ p q) t 0 0|
        ≤ Kt * t ^ 2 + 0 * (t * Real.sqrt t) := hbd
      _ = (C_H * (2 ^ n * C) * gaussDdim (8 * t) (0 : Point n)) * t ^ 2 := by
          rw [hKtdef]; ring
  · calc |heatConv H (fun σ p q => leviSeries E σ p q + E σ p q) t 0 0 / (pref * t ^ 2)|
        ≤ (Kt + 0 / Real.sqrt t) / |pref| := hrem
      _ = (C_H * (2 ^ n * C) * gaussDdim (8 * t) (0 : Point n)) / |pref| := by
          rw [zero_div, add_zero, hKtdef]

/-! ### 4. ★ The wired corrHigher smoke — fully instantiated at the capstone prefactor. -/

/-- **★ `smoke_corrHigher_wired` — the frozen `O(t²)` API FULLY INSTANTIATED at capstone-shaped
    data.**  From a `FatFrozenPackage` alone: at the WITNESS slice kernel
    `H = (a,·,ζ) ↦ G_{2a}(0−ζ)` (nonzero, banked domination `frozenK2Sharp_H_witness`) and the
    CAPSTONE prefactor `pref = (heatKernel1D t 0)^n` (exactly the `hCorrHigher` prefactor of
    `trueKernel_diagonal_a1_eq_R6`; positive, hence ≠ 0 — proved here), every gate of
    `corrHigher_O_t2_restored` fires JOINTLY: the equality shape `heatConv = pref·(t²·cRem)`
    with `|cRem|` BOUNDED by `C_t·G_{8t}(0)/pref` (the `8^{−n/2}`-normalized ratio).  All
    quantifiers/radii/gates discharged from the single record — no incompatibility.
    ⚠ `F` here is the FROZEN tail (the transport instantiation needs the bridge, §3). -/
theorem smoke_corrHigher_wired (P : FatFrozenPackage n) (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ C_t cRem : ℝ, 0 ≤ C_t ∧
      heatConv (fun a _ ζ => gaussDdim (2 * a) ((0 : Point n) - ζ))
          (fun σ p q => leviSeries (frozenDefectKernel P.κ P.rS) σ p q
              + frozenDefectKernel P.κ P.rS σ p q) t 0 0
        = (heatKernel1D t 0) ^ n * (t ^ 2 * cRem)
      ∧ |cRem| ≤ (C_t * gaussDdim (8 * t) (0 : Point n)) / |(heatKernel1D t 0) ^ n| := by
  obtain ⟨C_t, hCt, hall⟩ := corrHigher_O_t2_restored (n := n) P.κ P.rS P.hκ.le P.hrS.le
  have hW := frozenK2Sharp_H_witness (n := n) (le_trans one_le_two P.hn)
  have hk : 0 < heatKernel1D t 0 := by
    unfold heatKernel1D
    positivity
  have hpref : (heatKernel1D t 0) ^ n ≠ 0 := pow_ne_zero n (ne_of_gt hk)
  obtain ⟨heq, hbd, hrem⟩ := hall (fun a _ ζ => gaussDdim (2 * a) ((0 : Point n) - ζ)) 1
    zero_le_one (fun a ζ ha => hW.1 a ζ ha) (fun ζ => hW.2.1 ζ)
    ((heatKernel1D t 0) ^ n) t ht ht1 hpref
  exact ⟨C_t, _, hCt, heq, by simpa using hrem⟩

/-- **`smoke_corrHigher_wired_vanVleck` — the wire at the capstone's ACTUAL `H`.**  Same
    conclusion shape, with `H := vanVleckGatedWitness g^κ gi^κ …` (the parametrix the curved
    capstone convolves).  The endpoint-zero binder is DISCHARGED (`gatedWitness_time_zero`);
    the Gaussian domination `hHdom` is ⚠ CARRIED, LABELLED — it is the hAdom-family analytic
    pile, NOT banked (consistent with the curved capstone's own carried `hAdomHeat`); it is
    the single unbanked hypothesis on `H` in this slot. -/
theorem smoke_corrHigher_wired_vanVleck (P : FatFrozenPackage n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric P.κ) (curvedRNCInv P.κ) a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (C_H : ℝ) (hCH : 0 ≤ C_H)
    -- ⚠ CARRIED (labelled): Gaussian domination of the gated transport parametrix — the
    -- hAdom-family pile; the ONLY unbanked hypothesis on `H` in this slot.
    (hHdom : ∀ (a' : ℝ) (ζ : Point n), 0 < a' →
      |vanVleckGatedWitness (curvedRNCMetric P.κ) (curvedRNCInv P.κ) hChr hK S a b a' 0 ζ|
        ≤ C_H * gaussDdim (2 * a') ((0 : Point n) - ζ))
    (pref t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (hpref : pref ≠ 0) :
    ∃ C_t cRem : ℝ, 0 ≤ C_t ∧
      heatConv (vanVleckGatedWitness (curvedRNCMetric P.κ) (curvedRNCInv P.κ) hChr hK S a b)
          (fun σ p q => leviSeries (frozenDefectKernel P.κ P.rS) σ p q
              + frozenDefectKernel P.κ P.rS σ p q) t 0 0
        = pref * (t ^ 2 * cRem)
      ∧ |cRem| ≤ (C_H * C_t * gaussDdim (8 * t) (0 : Point n)) / |pref| := by
  obtain ⟨C_t, hCt, hall⟩ := corrHigher_O_t2_restored (n := n) P.κ P.rS P.hκ.le P.hrS.le
  have hn1 : 0 < n := lt_of_lt_of_le two_pos P.hn
  obtain ⟨heq, hbd, hrem⟩ := hall
    (vanVleckGatedWitness (curvedRNCMetric P.κ) (curvedRNCInv P.κ) hChr hK S a b)
    C_H hCH hHdom
    (fun ζ => gatedWitness_time_zero hn1 (curvedRNCMetric P.κ) (curvedRNCInv P.κ)
      hChr hK S a b 0 ζ)
    pref t ht ht1 hpref
  exact ⟨C_t, _, hCt, heq, hrem⟩

/-! ### 5. ★ The joint co-instantiation certificate. -/

/-- **★★ `smoke_coinstantiation` — the END-TO-END smoke certificate.**  For every `n ≥ 2` there
    is ONE `FatFrozenPackage` whose data SIMULTANEOUSLY: is genuinely curved (`κ < 0`), has
    genuinely nested radii `0 < rS < rK < rdomain`, contains the center in its compact base,
    has a genuinely nonzero frozen defect at the gate at every `τ ∈ (0,1]`, AND fires the full
    bounded-cRem `O(t²)` corrHigher conclusion at the capstone prefactor at every `t ∈ (0,1]`.
    All from the single record — the radii/measures/gates/quantifiers of J4-609→616 are JOINTLY
    instantiable with the capstone-shaped consumer.  NO incompatibility found at the frozen
    tail level; the two owed Props are `FrozenTransportBridge` and `K1TransportBudget` (§3).
    NOT `a₁ = R/6`. -/
theorem smoke_coinstantiation (n : ℕ) (hn : 2 ≤ n) :
    ∃ P : FatFrozenPackage n,
      P.κ < 0 ∧ 0 < P.rS ∧ P.rS < P.rK ∧ P.rK < P.rdomain
      ∧ (0 : Point n) ∈ Metric.closedBall (0 : Point n) P.rK
      ∧ (∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∃ p : Point n, frozenDefectKernel P.κ P.rS τ p 0 ≠ 0)
      ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
          ∃ C_t cRem : ℝ, 0 ≤ C_t ∧
            heatConv (fun a _ ζ => gaussDdim (2 * a) ((0 : Point n) - ζ))
                (fun σ p q => leviSeries (frozenDefectKernel P.κ P.rS) σ p q
                    + frozenDefectKernel P.κ P.rS σ p q) t 0 0
              = (heatKernel1D t 0) ^ n * (t ^ 2 * cRem)
            ∧ |cRem| ≤ (C_t * gaussDdim (8 * t) (0 : Point n))
                / |(heatKernel1D t 0) ^ n| := by
  obtain ⟨P⟩ := fatFrozenPackage_inhabited n hn
  exact ⟨P, P.hκ, P.hrS, P.hSK, P.hKd, P.hK0, P.hWitness,
    fun t ht ht1 => smoke_corrHigher_wired P t ht ht1⟩

end QIQTH.CoInstSmoke

section AxiomChecks
open QIQTH.CoInstSmoke
#print axioms fatFrozenPackage_inhabited
#print axioms gatedWitness_time_zero
#print axioms leviSeries_split
#print axioms tail_slice_of_pointwise
#print axioms bridged_tail_pointwise
#print axioms smoke_bridge_verdict
#print axioms smoke_corrHigher_wired
#print axioms smoke_corrHigher_wired_vanVleck
#print axioms smoke_coinstantiation
end AxiomChecks
