/-
  EquivProbe — J4-620: the EQUIVARIANCE PROBE for `hpkgBound`-at-fat-`K` — THE CORE READ VERDICT,
  the frame-defect obstruction pin at every off-center row, and the route-(c) first lemma
  (per-`q` whitening in CLOSED FORM).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`; this proves NOTHING about the coefficient VALUE.  `a₁ = R/6`
  remains CONDITIONAL (established non-vacuously ONLY for the FLAT tower); the curved side still owes
  `hpkgBound`-at-fat-`K` (this probe maps its true shape), `hEbound`/`hInt` at the transport kernel,
  the `K1TransportBudget`, the fat-`K` carrier piles, the capstone co-instantiation, and the prior
  analytic piles.

  ── ★★★ THE CORE READ VERDICT (J4-620, from reading the mainline statements — the brick's finding).

  1.  THE uniform* MACHINERY IS PER-`q`-UNIFORM, NOT CENTER-PINNED.  `uniformFlowExp g gi hC hK q`
      is the geodesic endpoint map FROM `q` (`UniformFlowNondeg.lean:167` — tube through `(q, w)`);
      `uniformInverseChart` (`UniformChartRadius.lean:228`) inverts it at a SINGLE radius over `K`;
      `uniformResidualN1_narrow_mixed_lin` (`CoeffU1Fix.lean:466`), `uniformResidual(-Linear)_
      gaussian_bound_tau_narrow` (`WidthMarginEngine.lean:343` / `CoeffU1Fix.lean:352`) and
      `cutoffResidualN1_uniformFlow_narrow_mixed_below_lin` (`CoeffU1Fix.lean:562`) all bind
      `∀ q ∈ K` with `K`-uniform constants.  The "uniform" in the names IS uniformity over the base
      point.  J4-619's difficulty estimate stands for a different reason (2. below).

  2.  WHERE `hframeK` REALLY ENTERS — the FRAME, not the BASE POINT.  In the whole residual chain
      `hframeK` (`∀ q ∈ K, g q = δ`) is consumed at EXACTLY ONE lemma:
      `uniformFlowPullbackMetricInv_dev_uniform` (`UniformFlowJetZero.lean:462`), the `O(r²)` decay
      `|g̃⁻¹_q(v) − δ| ≤ M·rncRadialSq v`.  The chart IS based at `q`, so the FIRST jet of the
      pullback vanishes for free (`uniformFlowPullbackMetric_pd_zero_center`, frame-free — the
      J4-604 observation), but the ZEROTH jet is `g̃_q(0) = g(q)` (`uniformFlowPullbackMetric_zero_
      center`, proved): the chart's frame at `q` is the AMBIENT COORDINATE frame, NOT a
      `g(q)`-orthonormal one.  `hframeK` compensates for the missing per-`q` frame WHITENING.

  3.  THE OBSTRUCTION IS IN THE WITNESS, NOT ONLY IN THE PROOFS.  The as-built witness
      (`vanVleckGatedWitness` → `globalCutoffParametrixWitnessN 1 … (uniformInverseChart …)` →
      `heatParametrix` → flat `gaussDdim` phase `|W_q p|²/4τ`) carries the EUCLIDEAN quadratic
      phase in the UNWHITENED chart coordinate.  Since `g̃_q(0) = g^κ(q) ≠ δ` at every `q ≠ 0`
      (formalized below: `uniformFlow_perq_chart_frame_defect`), the row-`q` heat defect at `p = q`
      contains the trace term `(tr g̃⁻¹_q(0) − n)/(2τ)·(4πτ)^{−n/2}` with nonzero coefficient
      (`curvedRNCInv_trace_defect_ne` below = the J4-608 diagonal witness AT EVERY OFF-CENTER ROW)
      — the same `ε₀/τ` floor as the center gauge, now shown to sit in the WITNESS phase itself.
      ⚠ CONSEQUENCE (assessment, lower bound not formalized here): fat-`K` `hpkgBound` for the
      AS-BUILT witness is plausibly FALSE at `κ ≠ 0`, refining Sol's J4-619 (β) "plausibly TRUE" —
      that verdict was conditioned on the phase being the per-`q` GEODESIC one, but the geodesic
      distance is `|v|_{g(q)}`, not `|v|`, and the coordinate-frame chart delivers `|v|`.

  4.  THE EQUIVARIANCE ROUTE COLLAPSES ONTO ROUTE (c) (per-`q` whitening).  (a) Exact-space-form
      equivariance does not apply to the as-built witness even at the exact space form: isometries
      map `g`-orthonormal frames to `g`-orthonormal frames, and the as-built witness is
      coordinate-framed — the isometry-conjugated row-0 analysis bounds the WHITENED witness, a
      DIFFERENT kernel.  (b) `g^κ` is not the exact space form anyway (J4-604: tangential
      eigenvalue `1 − (κ/3)r²` matches `(S_κ/r)²` only to `O(r⁴)`), so exact isometries are not
      isometries of `g^κ`.  Both objections land on the same repair, which is ALSO J4-608's route
      (c): re-base the witness with a per-`q` LINEAR whitening `E_q` (`E_qᵀ g(q) E_q = δ`), i.e.
      chart initial velocity `E_q w` / frozen-metric Gaussian `Γ_q`.  Then `g̃_q(0) = δ` holds BY
      CONSTRUCTION, the sole `hframeK` consumer (the dev bound) replays verbatim, and the banked
      per-`q`-uniform chain (1.) is re-entered without `hframeK`.  The whitening EXISTS IN CLOSED
      FORM for `g^κ` (rank-one structure): `E_q = a·δ + b·q qᵀ`, `a = (1 − (κ/3)|q|²)^{−1/2}`,
      `b = (1 − a)/|q|²` — proved below (`curvedRNC_whitening`).  What route (c) still OWES (the
      honest difficulty): re-running the chart/flow/jet layer for the whitened family (the
      Skolemized uniformFlow constants are per-metric; whitened = a `q`-family of charts of the
      SAME metric with rotated initial velocity — the tube machinery accepts arbitrary initial
      `w`, so the change is a PRE-COMPOSITION `w ↦ E_q w`, not a new metric), plus the coefficient
      bounds (layer 3) at the whitened profile.  This is strictly smaller than the J4-619
      "(hbound-fat)-class full per-`q` transport replay": the amplitude/coefficient layers were
      never `hframeK`-infected (they bind `∀ q ∈ K` already); the owed part is the phase/frame
      layer only.

  ── LANDED HERE (all std-3, no sorry):
    • `curvedRNCMetric_trace` / `curvedRNCMetric_trace_defect_ne` — closed trace of `g^κ(q)` and its
      defect `tr g^κ(q) − n = −(κ/3)(n−1)r² ≠ 0` for `κ ≠ 0`, `n ≥ 2`, `q ≠ 0`.
    • `curvedRNCInv_trace` / ★ `curvedRNCInv_trace_defect_ne` — closed trace of `gi^κ(q)` and the
      J4-608 diagonal-witness coefficient at EVERY off-center row:
      `tr gi^κ(q) − n = (κ/3)(n−1)r²/(1 − (κ/3)r²) ≠ 0` (`κ < 0`, `n ≥ 2`, `q ≠ 0`) — the
      previously-unformalized lower-bound seed of the `ε₀/τ` floor, now row-general.
    • ★★ `uniformFlow_perq_chart_frame_defect` — THE OBSTRUCTION PIN, stated on the MACHINERY'S OWN
      object: the per-`q` uniform-flow pullback metric of the genuinely-curved witness has
      `tr g̃_q(0) ≠ n` at every `q ≠ 0` in the base compact — the zeroth-jet δ-frame requirement of
      the sole `hframeK` consumer FAILS at every off-center row of the as-built chart.
    • ★★ `curvedRNC_whitening` (+ `curvedRNC_whitening_exists`) — route (c)'s first lemma: the
      per-`q` whitening of `g^κ` in closed form, `∑ₖ∑ₗ E_q(i,k)·g^κ(q)(k,l)·E_q(l,j) = δ_ij`, with
      `E_q` SYMMETRIC — the exact frame the whitened witness needs.
    • Non-vacuity gates: `equivProbe_offcenter_inhabited` (a genuinely curved, genuinely off-center
      instantiation of the defect theorems at `n = 2`, `κ = −1`, `q = (1,1)`);
      `curvedRNC_whitening_nondegenerate` (the whitening frame is NOT the identity at the same
      witness point — the lemma has genuinely non-δ content).

  No `sorry`, no `admit`, no new axioms, no `:= True`; no existing file edited except the
  `QIQTH.lean` / `AxiomAudit.lean` wiring; nothing committed.
-/
import Mathlib
import QIQTH.CurvedRNCGaugeBundle
import QIQTH.CurvedRNCPosDef
import QIQTH.CurvedA1CenterAmp

open Finset
open QIQTH.Curvature QIQTH.RadialDistance QIQTH.PullbackMetric
open QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedA1CenterAmp
open Set Filter
open scoped Topology BigOperators

namespace QIQTH.EquivProbe

variable {n : ℕ}

set_option maxHeartbeats 800000

/-! ### 1. Closed traces of the curved witness and its inverse. -/

/-- **The trace of `g^κ(q)` in closed form**: `∑ᵢ g^κ(q)ᵢᵢ = n − (κ/3)(n−1)·r²`. -/
theorem curvedRNCMetric_trace (K : ℝ) (q : Point n) :
    (∑ i, curvedRNCMetric K q i i)
      = (n : ℝ) - K / 3 * ((n : ℝ) - 1) * rncRadialSq q := by
  have h : ∀ i : Fin n, curvedRNCMetric K q i i
      = 1 - K / 3 * rncRadialSq q + K / 3 * (q i) ^ 2 := by
    intro i
    simp only [curvedRNCMetric, eq_self_iff_true, if_true]
    ring
  rw [Finset.sum_congr rfl fun i _ => h i]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    ← Finset.mul_sum]
  rw [show (∑ i, (q i) ^ 2) = rncRadialSq q from rfl]
  ring

/-- **The trace defect of `g^κ` at every off-center point**: `tr g^κ(q) ≠ n` for `κ ≠ 0`, `n ≥ 2`,
    `q ≠ 0` — the per-`q` chart frame `g̃_q(0) = g^κ(q)` is NOT `δ` at any off-center row. -/
theorem curvedRNCMetric_trace_defect_ne (K : ℝ) (hK : K ≠ 0) (hn : 2 ≤ n)
    (q : Point n) (hq : q ≠ 0) :
    (∑ i, curvedRNCMetric K q i i) ≠ (n : ℝ) := by
  rw [curvedRNCMetric_trace]
  intro hEq
  have hr : 0 < rncRadialSq q := rncRadialSq_pos hq
  have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hzero : K / 3 * ((n : ℝ) - 1) * rncRadialSq q = 0 := by linarith
  have hK3 : K / 3 ≠ 0 := div_ne_zero hK (by norm_num)
  have h1 : ((n : ℝ) - 1) ≠ 0 := by linarith
  exact (mul_ne_zero (mul_ne_zero hK3 h1) hr.ne') hzero

/-- **The trace of `gi^κ(q)` in closed form**:
    `∑ᵢ gi^κ(q)ᵢᵢ = (1/(1 − (κ/3)r²))·(n − (κ/3)r²)`. -/
theorem curvedRNCInv_trace (K : ℝ) (q : Point n) :
    (∑ i, curvedRNCInv K q i i)
      = (1 / (1 - K / 3 * rncRadialSq q)) * ((n : ℝ) - K / 3 * rncRadialSq q) := by
  have h : ∀ i : Fin n, curvedRNCInv K q i i
      = (1 / (1 - K / 3 * rncRadialSq q)) * (1 - K / 3 * (q i) ^ 2) := by
    intro i
    simp only [curvedRNCInv, eq_self_iff_true, if_true]
    ring
  rw [Finset.sum_congr rfl fun i _ => h i, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    ← Finset.mul_sum]
  rw [show (∑ i, (q i) ^ 2) = rncRadialSq q from rfl]

/-- **★ THE ROW-`q` DIAGONAL-WITNESS COEFFICIENT (J4-608, formalized at every off-center row).**
    `tr gi^κ(q) ≠ n` for `κ < 0`, `n ≥ 2`, `q ≠ 0`.  This is the nonvanishing of the leading
    `1/τ`-defect coefficient `(tr g̃⁻¹_q(0) − n)/2` of the flat-phase parametrix at row `q` — the
    `ε₀/τ` floor of the center gauge, exhibited as a property of EVERY off-center row of the
    as-built (coordinate-framed) witness, not of the center replay only. -/
theorem curvedRNCInv_trace_defect_ne (K : ℝ) (hK : K < 0) (hn : 2 ≤ n)
    (q : Point n) (hq : q ≠ 0) :
    (∑ i, curvedRNCInv K q i i) ≠ (n : ℝ) := by
  rw [curvedRNCInv_trace]
  intro hEq
  have hr : 0 < rncRadialSq q := rncRadialSq_pos hq
  set r2 : ℝ := rncRadialSq q with hr2
  have hc : K / 3 * r2 < 0 := mul_neg_of_neg_of_pos (by linarith) hr
  have hα : (0 : ℝ) < 1 - K / 3 * r2 := by linarith
  have hn1 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- clear the denominator: `n − c = n·(1 − c)` with `c = (K/3)r² < 0` forces `c·(n−1) = 0`.
  rw [div_mul_eq_mul_div, one_mul, div_eq_iff hα.ne'] at hEq
  have hzero : K / 3 * r2 * ((n : ℝ) - 1) = 0 := by ring_nf at hEq ⊢; linarith
  have h1 : ((n : ℝ) - 1) ≠ 0 := by linarith
  exact (mul_ne_zero hc.ne h1) hzero

/-! ### 2. ★★ The obstruction pin on the machinery's own object. -/

/-- **★★ THE FRAME-DEFECT OBSTRUCTION PIN.**  For the genuinely-curved witness
    `g^κ = curvedRNCMetric κ` (`κ ≠ 0`, `n ≥ 2`) and ANY compact base `Kset`, the per-`q`
    uniform-flow pullback metric — the machinery's OWN chart-origin zeroth jet — satisfies
    `tr g̃_q(0) ≠ n` at every off-center `q ∈ Kset`.  Via the proven value jet
    `uniformFlowPullbackMetric_zero_center` (`g̃_q(0) = g(q)`, frame-free) + the closed trace.
    CONSEQUENCE: the δ-frame requirement of the SOLE `hframeK` consumer of the residual chain
    (`uniformFlowPullbackMetricInv_dev_uniform`'s zeroth jet) FAILS at every off-center row —
    the per-`q`-uniform machinery is blocked at fat `K` by the FRAME, not by the base point;
    and the as-built flat-phase witness inherits the row-`q` `ε₀/τ` defect floor
    (`curvedRNCInv_trace_defect_ne`).  NOT `a₁ = R/6`. -/
theorem uniformFlow_perq_chart_frame_defect (K : ℝ) (hK : K ≠ 0) (hn : 2 ≤ n)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric K) (curvedRNCInv K) a b c y))
    {Kset : Set (Point n)} (hKc : IsCompact Kset)
    (q : Point n) (hq : q ∈ Kset) (hq0 : q ≠ 0) :
    (∑ i, uniformFlowPullbackMetric (curvedRNCMetric K) (curvedRNCInv K) hChr hKc q 0 i i)
      ≠ (n : ℝ) := by
  have hval : ∀ i : Fin n,
      uniformFlowPullbackMetric (curvedRNCMetric K) (curvedRNCInv K) hChr hKc q 0 i i
        = curvedRNCMetric K q i i := fun i =>
    uniformFlowPullbackMetric_zero_center (curvedRNCMetric K) (curvedRNCInv K) hChr hKc q hq i i
  rw [Finset.sum_congr rfl fun i _ => hval i]
  exact curvedRNCMetric_trace_defect_ne K hK hn q hq0

/-! ### 3. ★★ Route (c)'s first lemma — the per-`q` whitening in closed form. -/

/-- **The closed-form whitening frame** `E_q = a·δ + b·q qᵀ` for `g^κ(q)`:
    `a = (1 − (κ/3)|q|²)^{−1/2}` (tangential), `b = (1 − a)/|q|²` (fixes the radial eigenvalue
    to `1`; recall the radial eigenvalue of `g^κ(q)` is exactly `1`). -/
noncomputable def curvedWhitening (K : ℝ) (q : Point n) : Fin n → Fin n → ℝ :=
  fun i j =>
    (1 / Real.sqrt (1 - K / 3 * rncRadialSq q)) * (if i = j then (1 : ℝ) else 0)
      + ((1 - 1 / Real.sqrt (1 - K / 3 * rncRadialSq q)) / rncRadialSq q) * q i * q j

/-- The whitening frame is symmetric. -/
theorem curvedWhitening_symm (K : ℝ) (q : Point n) (i j : Fin n) :
    curvedWhitening K q i j = curvedWhitening K q j i := by
  simp only [curvedWhitening]
  by_cases h : i = j
  · subst h; ring
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]; ring

/-- **★★ ROUTE (c) FIRST LEMMA — the per-`q` whitening identity in CLOSED FORM.**
    For `κ ≤ 0` and every `q ≠ 0`:  `∑ₖ ∑ₗ E(i,k) · g^κ(q)(k,l) · E(l,j) = δ_ij` with
    `E = curvedWhitening κ q` — the exact `E_qᵀ g(q) E_q = δ` frame normalization whose absence
    is the sole `hframeK` obstruction (see `uniformFlow_perq_chart_frame_defect`).  The proof is
    the rank-one algebra: `g^κ(q) = α·δ + (κ/3)·q qᵀ` with `α = 1 − (κ/3)r²`, `E = a·δ + b·q qᵀ`,
    `a²α = 1`, `a + b·r² = 1`, and the cross coefficient cancels exactly
    (`α·b·(1+a) + κ/3 = (α − α a²)/r² + κ/3 = (α − 1)/r² + κ/3 = 0`).  NOT `a₁ = R/6`. -/
theorem curvedRNC_whitening (K : ℝ) (hK : K ≤ 0) (q : Point n) (hq : q ≠ 0) (i j : Fin n) :
    (∑ k, ∑ l, curvedWhitening K q i k * curvedRNCMetric K q k l * curvedWhitening K q l j)
      = if i = j then (1 : ℝ) else 0 := by
  classical
  set r2 : ℝ := rncRadialSq q with hr2def
  have hr : 0 < r2 := rncRadialSq_pos hq
  set α : ℝ := 1 - K / 3 * r2 with hαdef
  have hα : (1 : ℝ) ≤ α := by
    have : 0 ≤ -(K / 3) * r2 := mul_nonneg (by linarith) hr.le
    simp only [hαdef]; linarith
  have hα0 : (0 : ℝ) < α := lt_of_lt_of_le one_pos hα
  set a : ℝ := 1 / Real.sqrt α with hadef
  have hsq : Real.sqrt α > 0 := Real.sqrt_pos.mpr hα0
  have ha0 : 0 < a := by positivity
  have haα : a ^ 2 * α = 1 := by
    rw [hadef, div_pow, one_pow, Real.sq_sqrt hα0.le]
    field_simp
  set b : ℝ := (1 - a) / r2 with hbdef
  have hs : a + b * r2 = 1 := by
    rw [hbdef, div_mul_cancel₀ _ hr.ne']
    ring
  -- the metric in rank-one form.
  have hg : ∀ k l : Fin n, curvedRNCMetric K q k l
      = α * (if k = l then (1 : ℝ) else 0) + K / 3 * q k * q l := by
    intro k l
    simp only [curvedRNCMetric, hαdef, ← hr2def]
    by_cases h : k = l
    · subst h; simp only [if_pos rfl]; ring
    · simp only [if_neg h]; ring
  have hE : ∀ k l : Fin n, curvedWhitening K q k l
      = a * (if k = l then (1 : ℝ) else 0) + b * q k * q l := by
    intro k l
    simp only [curvedWhitening, hadef, hbdef, hαdef, ← hr2def]
  have hqsum : (∑ l, q l * q l) = r2 := by
    rw [hr2def]; simp only [rncRadialSq]; exact Finset.sum_congr rfl fun l _ => (sq (q l)).symm
  -- inner contraction: `(g·E)(k,j) = α·a·δ_kj + c₂·q_k·q_j` with `c₂ = α·b + (κ/3)·(a + b·r²)`.
  set c₂ : ℝ := α * b + K / 3 * (a + b * r2) with hc₂def
  have hinner : ∀ k : Fin n, (∑ l, curvedRNCMetric K q k l * curvedWhitening K q l j)
      = α * a * (if k = j then (1 : ℝ) else 0) + c₂ * q k * q j := by
    intro k
    have hS1 : (∑ l, α * a * ((if k = l then (1 : ℝ) else 0) * (if l = j then (1 : ℝ) else 0)))
        = α * a * (if k = j then (1 : ℝ) else 0) := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro l _ hl
        rw [if_neg (fun h => hl h.symm), zero_mul, mul_zero]
      · intro h; exact absurd (Finset.mem_univ k) h
    have hS2 : (∑ l, α * b * ((if k = l then (1 : ℝ) else 0) * (q l * q j)))
        = α * b * (q k * q j) := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro l _ hl
        rw [if_neg (fun h => hl h.symm), zero_mul, mul_zero]
      · intro h; exact absurd (Finset.mem_univ k) h
    have hS3 : (∑ l, K / 3 * a * (q k * (q l * (if l = j then (1 : ℝ) else 0))))
        = K / 3 * a * (q k * q j) := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro l _ hl
        rw [if_neg hl, mul_zero, mul_zero, mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    have hS4 : (∑ l, K / 3 * b * (q k * (q l * q l) * q j))
        = K / 3 * b * (q k * r2 * q j) := by
      have hpull : (∑ l, K / 3 * b * (q k * (q l * q l) * q j))
          = K / 3 * b * (q k * q j) * (∑ l, q l * q l) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [hpull, hqsum]; ring
    calc (∑ l, curvedRNCMetric K q k l * curvedWhitening K q l j)
        = ∑ l, (α * a * ((if k = l then (1 : ℝ) else 0) * (if l = j then (1 : ℝ) else 0))
            + α * b * ((if k = l then (1 : ℝ) else 0) * (q l * q j))
            + K / 3 * a * (q k * (q l * (if l = j then (1 : ℝ) else 0)))
            + K / 3 * b * (q k * (q l * q l) * q j)) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hg k l, hE l j]; ring
      _ = α * a * (if k = j then (1 : ℝ) else 0) + c₂ * q k * q j := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
            hS1, hS2, hS3, hS4, hc₂def]
          ring
  -- outer contraction.
  have houter : (∑ k, ∑ l, curvedWhitening K q i k * curvedRNCMetric K q k l
        * curvedWhitening K q l j)
      = a * (α * a) * (if i = j then (1 : ℝ) else 0)
        + (a * c₂ + b * (α * a) + b * c₂ * r2) * (q i * q j) := by
    have hT1 : (∑ k, a * (α * a)
          * ((if i = k then (1 : ℝ) else 0) * (if k = j then (1 : ℝ) else 0)))
        = a * (α * a) * (if i = j then (1 : ℝ) else 0) := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk
        rw [if_neg (fun h => hk h.symm), zero_mul, mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    have hT2 : (∑ k, a * c₂ * ((if i = k then (1 : ℝ) else 0) * (q k * q j)))
        = a * c₂ * (q i * q j) := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hk
        rw [if_neg (fun h => hk h.symm), zero_mul, mul_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    have hT3 : (∑ k, b * (α * a) * (q i * (q k * (if k = j then (1 : ℝ) else 0))))
        = b * (α * a) * (q i * q j) := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        rw [if_neg hk, mul_zero, mul_zero, mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    have hT4 : (∑ k, b * c₂ * (q i * (q k * q k) * q j))
        = b * c₂ * (q i * r2 * q j) := by
      have hpull : (∑ k, b * c₂ * (q i * (q k * q k) * q j))
          = b * c₂ * (q i * q j) * (∑ k, q k * q k) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [hpull, hqsum]; ring
    calc (∑ k, ∑ l, curvedWhitening K q i k * curvedRNCMetric K q k l * curvedWhitening K q l j)
        = ∑ k, curvedWhitening K q i k
            * (∑ l, curvedRNCMetric K q k l * curvedWhitening K q l j) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
      _ = ∑ k, (a * (α * a) * ((if i = k then (1 : ℝ) else 0) * (if k = j then (1 : ℝ) else 0))
            + a * c₂ * ((if i = k then (1 : ℝ) else 0) * (q k * q j))
            + b * (α * a) * (q i * (q k * (if k = j then (1 : ℝ) else 0)))
            + b * c₂ * (q i * (q k * q k) * q j)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hinner k, hE i k]; ring
      _ = a * (α * a) * (if i = j then (1 : ℝ) else 0)
            + (a * c₂ + b * (α * a) + b * c₂ * r2) * (q i * q j) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
            hT1, hT2, hT3, hT4]
          ring
  rw [houter]
  -- scalar endgame: `a·(α·a) = 1` and the cross coefficient vanishes.
  have hdiag : a * (α * a) = 1 := by rw [show a * (α * a) = a ^ 2 * α by ring, haα]
  have hcross : a * c₂ + b * (α * a) + b * c₂ * r2 = 0 := by
    have hb1 : b * r2 = 1 - a := by rw [hbdef]; field_simp
    have hcoef : c₂ = α * b + K / 3 := by rw [hc₂def, hs]; ring
    -- `α·b·(1+a) + κ/3 = 0`  ⟸  `α − α·a² = 1 − ... `: from `a²α = 1`, `α·(1−a)(1+a) = α − 1 = −(κ/3)r²`.
    have hkey : α * b * (1 + a) + K / 3 = 0 := by
      have hexp : α * (1 - a) * (1 + a) = α - 1 := by
        have : α * (1 - a) * (1 + a) = α - α * a ^ 2 := by ring
        rw [this, show α * a ^ 2 = 1 by linarith [haα]]
      have hα1 : α - 1 = -(K / 3) * r2 := by rw [hαdef]; ring
      have : α * b * (1 + a) * r2 = (α - 1) := by
        calc α * b * (1 + a) * r2 = α * (b * r2) * (1 + a) := by ring
          _ = α * (1 - a) * (1 + a) := by rw [hb1]
          _ = α - 1 := hexp
      have hKr : α * b * (1 + a) * r2 = -(K / 3) * r2 := by rw [this, hα1]
      have := mul_right_cancel₀ hr.ne' hKr
      linarith
    calc a * c₂ + b * (α * a) + b * c₂ * r2
        = c₂ * (a + b * r2) + α * a * b := by ring
      _ = c₂ + α * a * b := by rw [hs]; ring
      _ = α * b + K / 3 + α * a * b := by rw [hcoef]
      _ = α * b * (1 + a) + K / 3 := by ring
      _ = 0 := hkey
  rw [hdiag, hcross]
  ring

/-- **Route (c) whitening — the existence form** (symmetric frame + the δ-normalization),
    packaged the way a whitened-chart brick would consume it. -/
theorem curvedRNC_whitening_exists (K : ℝ) (hK : K ≤ 0) (q : Point n) (hq : q ≠ 0) :
    ∃ E : Fin n → Fin n → ℝ, (∀ i j, E i j = E j i) ∧
      ∀ i j, (∑ k, ∑ l, E i k * curvedRNCMetric K q k l * E l j)
        = if i = j then (1 : ℝ) else 0 :=
  ⟨curvedWhitening K q, curvedWhitening_symm K q,
    fun i j => curvedRNC_whitening K hK q hq i j⟩

/-! ### 4. Non-vacuity gates (cp466 discipline). -/

/-- The off-center witness point at `n = 2`: `q = (1,1) ≠ 0`. -/
noncomputable def probeQ : Point 2 := fun _ => 1

theorem probeQ_ne_zero : probeQ ≠ 0 := by
  intro h
  have h0 : probeQ 0 = 0 := by rw [h]; rfl
  simp [probeQ] at h0

/-- **Non-vacuity gate: the defect theorems are inhabited at a genuinely curved (`κ = −1`),
    genuinely off-center (`q = (1,1) ≠ 0`) instantiation** — both trace defects are realized. -/
theorem equivProbe_offcenter_inhabited :
    (∑ i, curvedRNCMetric (-1 : ℝ) probeQ i i) ≠ ((2 : ℕ) : ℝ) ∧
    (∑ i, curvedRNCInv (-1 : ℝ) probeQ i i) ≠ ((2 : ℕ) : ℝ) :=
  ⟨curvedRNCMetric_trace_defect_ne (-1) (by norm_num) le_rfl probeQ probeQ_ne_zero,
   curvedRNCInv_trace_defect_ne (-1) (by norm_num) le_rfl probeQ probeQ_ne_zero⟩

/-- **Non-vacuity gate: the whitening frame is genuinely non-trivial** — at the same curved
    off-center witness, `E ≠ δ` (its `(0,0)` entry differs from `1`): the route-(c) lemma is not
    inhabited by the identity frame. -/
theorem curvedRNC_whitening_nondegenerate :
    curvedWhitening (-1 : ℝ) probeQ 0 0 ≠ (1 : ℝ) := by
  have hr2 : rncRadialSq probeQ = 2 := by
    simp [rncRadialSq, probeQ]
  have hval : curvedWhitening (-1 : ℝ) probeQ 0 0
      = 1 / Real.sqrt (5 / 3) + (1 - 1 / Real.sqrt (5 / 3)) / 2 := by
    simp only [curvedWhitening, hr2, probeQ, eq_self_iff_true, if_true]
    norm_num
  have hsq : Real.sqrt (5 / 3 : ℝ) > 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have ha : 1 / Real.sqrt (5 / 3 : ℝ) < 1 := by
    rw [div_lt_one (lt_trans one_pos hsq)]; exact hsq
  rw [hval]
  intro h
  -- entry `= a + (1−a)/2` with `a < 1` ⟹ `< 1`.
  linarith [ha]

end QIQTH.EquivProbe

section AxiomChecks
open QIQTH.EquivProbe
#print axioms QIQTH.EquivProbe.curvedRNCMetric_trace
#print axioms QIQTH.EquivProbe.curvedRNCMetric_trace_defect_ne
#print axioms QIQTH.EquivProbe.curvedRNCInv_trace
#print axioms QIQTH.EquivProbe.curvedRNCInv_trace_defect_ne
#print axioms QIQTH.EquivProbe.uniformFlow_perq_chart_frame_defect
#print axioms QIQTH.EquivProbe.curvedRNC_whitening
#print axioms QIQTH.EquivProbe.curvedRNC_whitening_exists
#print axioms QIQTH.EquivProbe.equivProbe_offcenter_inhabited
#print axioms QIQTH.EquivProbe.curvedRNC_whitening_nondegenerate
end AxiomChecks
