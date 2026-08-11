/-
  CurvedA1CenterAmp — J4-604: FIRST layer of the (hbound-fat) wall — the CENTER-ONLY-GAUGE variant of
  the uniform-flow pullback inverse-metric deviation bound, on the fat base compact
  `K = Metric.closedBall 0 r`, instantiated at the genuinely-curved witness `g^κ = curvedRNCMetric κ`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`; this proves NOTHING about the coefficient.  `a₁ = R/6`
  remains CONDITIONAL (established non-vacuously ONLY for the FLAT tower); the curved re-base still
  owes (hbound-fat) + fat-`K` `hEmeas` + `hAdom` + `hcont` + the co-instantiated capstone application
  + the prior analytic piles / convergence trio / `hmassone` pre-ρ carriers / `hjets` residual.
  This brick is the FIRST layer of the (hbound-fat) producer rework, not its closure.

  ── ★★ THE USE-SITE VERDICT (proved by construction, the point of this brick).
  In the banked `UniformFlowJetZero.uniformFlowPullbackMetricInv_dev_uniform` the per-`q` frame
  normalisation `hframeK : ∀ q ∈ K, g q = δ` is INITIAL-CONDITION-ONLY: it enters the proof solely
  through the flow-time-0 value jet `g̃_q(0) = g(q)` (`expPullbackMetric_at_zero` through the weld),
  which `hframeK` collapses to `δ`.  The other three pillars are FRAME-FREE:
    • the first-derivative jet `∂g̃_q(0) = 0` (`pd_expPullbackMetric_at_zero` — RNC-radiality, no
      `hframe` in its hypotheses);
    • the uniform `C²` packet (`uniformFlowPullbackMetric_c2_uniform_full` — no `hframeK`);
    • the uniform inverse bound (`uniformInverseMetric_bound` — no `hframeK`).
  Hence the center-gauge replay below replaces `hframeK` by the quantitative frame deviation
  `hdevK : ∀ q ∈ K, ∀ i j, |g(q)ᵢⱼ − δᵢⱼ| ≤ ε₀` and pays EXACTLY `+ε₀`:
    forward   `|g̃_q(v)ᵢⱼ − δᵢⱼ| ≤ M·‖v‖² + ε₀`         (`uniformFlowPullbackMetric_dev_uniform_center`)
    inverse   `|g̃⁻¹_q(v)ᵢⱼ − δᵢⱼ| ≤ M·(rncRadialSq v + ε₀)` (`uniformFlowPullbackMetricInv_dev_uniform_center`)
  with radius `r₀` and constant `M` produced BEFORE `ε₀` is quantified — `M` is INDEPENDENT of `ε₀`
  (no ε₀-inflation of the Grönwall/packet constants; only the additive floor moves).

  ── THE HONEST SUPPLIER (foundation stone).  For the curved witness the frame deviation is EXPLICIT
  from the closed form `g^κ(x)ᵢⱼ = δᵢⱼ − (κ/3)(‖x‖²δᵢⱼ − xᵢxⱼ)`:
    `curvedRNC_frame_dev_pointwise` :  `|g^κ(x)ᵢⱼ − δᵢⱼ| ≤ (|κ|/3)·rncRadialSq x`
    `curvedRNC_frame_dev_on_ball`   :  `≤ (|κ|/3)·(n·r²)` for `x ∈ closedBall 0 r` (sup-norm chart,
                                        `rncRadialSq ≤ n·‖x‖²_∞`) — the `hdevK` instance at fat `K`.
  Constant honesty: diagonal entries deviate by `(|κ|/3)(‖x‖² − xᵢ²) ≤ (|κ|/3)‖x‖²`, off-diagonal by
  `(|κ|/3)|xᵢxⱼ| ≤ (|κ|/3)·(xᵢ²+xⱼ²)/2 ≤ (|κ|/3)‖x‖²` — the bound is entrywise-sharp up to the
  AM–GM/coordinate slack, NOT an `≤ ∞` placebo.

  ── ★★ THE FAT-`K` CURVED INSTANTIATION.  `curvedRNC_pullbackInv_dev_uniform_center`: for `κ ≤ 0`
  and EVERY radius `r`, on `K = closedBall 0 r` the inverse pullback-metric deviation bound HOLDS at
  the curved witness with `ε₀ = (|κ|/3)·n·r²` — all carries discharged from banked curved lemmas
  (`curvedRNCMetric_contDiff`, `hgnd_of_hgpos ∘ curvedRNCMetric_hgpos`, `curvedRNCMetric_symm`,
  `curvedRNCMetric_hinvF`, and `hChr` via `christoffel_contDiff` = `curvedRNC_hChr`).  This is the
  exact deviation input that the J4-603 wall map lists FIRST among the `hframeK` use-sites
  (`uniformFlowPullbackMetricInv_dev_uniform`) — now available at fat `K` WITHOUT `hframeK`.

  ── NON-VACUITY (the cp466 discipline).  `curvedRNC_center_gauge_satisfiable`: at every `r > 0`,
  `n ≥ 1` the base compact contains a NONZERO point (no `K ⊆ {0}` collapse — contrast
  `rebased_hframeK_unsat`, J4-603) AND `hdevK` holds with the explicit `ε₀`;
  `curvedRNC_center_eps_arbitrarily_small`: the required `ε₀` can be made `< ε` for ANY `ε > 0` by
  shrinking `r` — the smallness a future consumer needs is achievable while `K` stays fat.

  ── REMAINING (hbound-fat) LAYERS (scoped, OPEN — in dependency order):
    1. center-gauge `uniformFlowChristoffel_linear_decay` (Γ̃-decay: `hframeK` again via the base jet),
    2. center-gauge `uniformCoeff_bound` / `uniformCoeffLinear_bound` (amplitude coefficients),
    3. center-gauge `uniformResidual(_Linear)_gaussian_bound_tau_narrow` (τ-narrow residuals),
    4. re-assembly of `cutoffResidualN1_uniformFlow_narrow_mixed_below_lin` →
       `gatedWitnessN1_hEboundW_le_lin_CONST` → the fat-`K` `curvedRNC_heatOp_dom_pkg` analogue
       (the (hbound-fat) producer itself), with the `ε₀`-terms tracked through the width-2 Gaussian
       bookkeeping.

  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous antecedent posing as a discharge;
  no existing file edited except the `QIQTH.lean` / `AxiomAudit.lean` wiring; nothing committed.
-/
import Mathlib
import QIQTH.UniformFlowJetZero
import QIQTH.CurvedRNCGaugeBundle
import QIQTH.CurvedRNCPosDef
import QIQTH.OuterCarryRecon
import QIQTH.ChristoffelSmooth

open QIQTH.Curvature QIQTH.PullbackMetric QIQTH.RadialDistance QIQTH.RNCDecay
open QIQTH.ExpMap QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedRNCPosDef QIQTH.OuterCarryRecon
open Set Filter
open scoped Topology BigOperators

namespace QIQTH.CurvedA1CenterAmp

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### The honest frame-deviation supplier for the curved witness. -/

/-- **Pointwise frame deviation of the curved witness.**  From the closed form
    `g^κ(x)ᵢⱼ = δᵢⱼ − (κ/3)(rncRadialSq x · δᵢⱼ − xᵢxⱼ)`:
    `|g^κ(x)ᵢⱼ − δᵢⱼ| ≤ (|κ|/3) · rncRadialSq x`.  Diagonal: `rncRadialSq x − xᵢ² ∈ [0, rncRadialSq x]`;
    off-diagonal: `|xᵢxⱼ| ≤ (xᵢ² + xⱼ²)/2 ≤ rncRadialSq x` (AM–GM + two-term subsum).  NOT `a₁ = R/6`. -/
theorem curvedRNC_frame_dev_pointwise (K : ℝ) (x : Point n) (i j : Fin n) :
    |curvedRNCMetric K x i j - (if i = j then (1 : ℝ) else 0)|
      ≤ |K| / 3 * rncRadialSq x := by
  have hdev : curvedRNCMetric K x i j - (if i = j then (1 : ℝ) else 0)
      = -(K / 3) * (rncRadialSq x * (if i = j then (1 : ℝ) else 0) - x i * x j) := by
    simp only [curvedRNCMetric]; ring
  have h3 : |K / 3| = |K| / 3 := by
    rw [abs_div]; norm_num
  rw [hdev, abs_mul, abs_neg, h3]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, mul_one]
    have hle : x i * x i ≤ rncRadialSq x := by
      have h1 : x i ^ 2 ≤ ∑ k, x k ^ 2 :=
        Finset.single_le_sum (fun k _ => sq_nonneg (x k)) (Finset.mem_univ i)
      calc x i * x i = x i ^ 2 := (pow_two (x i)).symm
        _ ≤ ∑ k, x k ^ 2 := h1
        _ = rncRadialSq x := rfl
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    have := mul_self_nonneg (x i)
    linarith
  · rw [if_neg h, mul_zero, zero_sub, abs_neg, abs_mul]
    have hr : rncRadialSq x = ∑ k, x k ^ 2 := rfl
    rw [hr]
    have hsum : x i ^ 2 + x j ^ 2 ≤ ∑ k, x k ^ 2 := by
      have hsub := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ ({i, j} : Finset (Fin n))) (fun k _ _ => sq_nonneg (x k))
      rwa [Finset.sum_pair h] at hsub
    nlinarith [sq_abs (x i), sq_abs (x j), abs_nonneg (x i), abs_nonneg (x j),
      sq_nonneg (|x i| - |x j|),
      Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) => sq_nonneg (x k))]

/-- **The coordinate-sum radius on the sup-norm ball.**  `q ∈ closedBall 0 r` (sup-norm chart
    `Point n = Fin n → ℝ`) forces `rncRadialSq q = ∑ᵢ qᵢ² ≤ n·r²`.  NOT `a₁ = R/6`. -/
theorem rncRadialSq_le_of_mem_closedBall {r : ℝ} {q : Point n}
    (hq : q ∈ Metric.closedBall (0 : Point n) r) :
    rncRadialSq q ≤ (n : ℝ) * r ^ 2 := by
  rw [Metric.mem_closedBall, dist_zero_right] at hq
  have hcoord : ∀ k : Fin n, q k ^ 2 ≤ r ^ 2 := by
    intro k
    have h1 : |q k| ≤ ‖q‖ := by
      have := norm_le_pi_norm q k
      simpa [Real.norm_eq_abs] using this
    have h2 : |q k| ≤ r := le_trans h1 hq
    calc q k ^ 2 = |q k| ^ 2 := (sq_abs _).symm
      _ ≤ r ^ 2 := by nlinarith [abs_nonneg (q k)]
  calc rncRadialSq q = ∑ k, q k ^ 2 := rfl
    _ ≤ ∑ _k : Fin n, r ^ 2 := Finset.sum_le_sum (fun k _ => hcoord k)
    _ = (n : ℝ) * r ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **★ The `hdevK` instance at the fat base compact** — the foundation stone of the (hbound-fat)
    center-gauge rework: on `K = closedBall 0 r` the curved witness deviates from `δ` by at most
    `ε₀ = (|κ|/3)·n·r²`, ENTRYWISE, at EVERY base point.  This is exactly the frame-deviation
    hypothesis the center-gauge deviation bounds below consume — satisfiable at every fat `K`, in
    contrast to `hframeK` (which forces `K ⊆ {0}`, `rebased_hframeK_unsat`, J4-603).
    NOT `a₁ = R/6`. -/
theorem curvedRNC_frame_dev_on_ball (K r : ℝ) :
    ∀ q ∈ Metric.closedBall (0 : Point n) r, ∀ i j : Fin n,
      |curvedRNCMetric K q i j - (if i = j then (1 : ℝ) else 0)|
        ≤ |K| / 3 * ((n : ℝ) * r ^ 2) := by
  intro q hq i j
  exact le_trans (curvedRNC_frame_dev_pointwise K q i j)
    (mul_le_mul_of_nonneg_left (rncRadialSq_le_of_mem_closedBall hq) (by positivity))

/-! ### The center-gauge jets: value jet `g̃(0) = g(q)` (no frame), pd-jet `∂g̃(0) = 0` (frame-free). -/

/-- **The flow-time-0 value jet WITHOUT the frame hypothesis.**  `g̃_q(0)ᵢⱼ = g(q)ᵢⱼ` — the weld
    transfer (`uniformFlowPullbackMetric_eq_expPullbackMetric_eventually`, at `0`) composed with
    `expPullbackMetric_at_zero`.  This isolates the SOLE `hframeK` use-site of the banked
    `uniformFlowPullbackMetricInv_dev_uniform`: `hframeK` only ever collapsed this value to `δ`.
    NOT `a₁ = R/6`. -/
theorem uniformFlowPullbackMetric_zero_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (q : Point n) (hq : q ∈ K) (i j : Fin n) :
    uniformFlowPullbackMetric g gi hC hK q 0 i j = g q i j := by
  have hB := uniformFlowPullbackMetric_eq_expPullbackMetric_eventually g gi hC hK q hq
  have h0 := hB.self_of_nhds
  rw [h0 i j, expPullbackMetric_at_zero g gi hC q i j]

/-- **The first-derivative jet at `0` is FRAME-FREE.**  `∂ₑ g̃_q(0)ᵢⱼ = 0` for every `q ∈ K` with NO
    frame normalisation at `q` — germ transfer through the weld (`pd_congr_eventuallyEq`) onto the
    proven `expPullbackMetric` jet (`pd_expPullbackMetric_at_zero`, whose hypotheses are only
    `hgsymm`/`hinv(q)`/`hg`).  This is the load-bearing observation of J4-604: the RNC radial gauge
    kills `∂g̃(0)` at EVERY base point, δ-frame or not.  NOT `a₁ = R/6`. -/
theorem uniformFlowPullbackMetric_pd_zero_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (q : Point n) (hq : q ∈ K) (i j e : Fin n) :
    pd (fun v => uniformFlowPullbackMetric g gi hC hK q v i j) e (0 : Point n) = 0 := by
  have hB := uniformFlowPullbackMetric_eq_expPullbackMetric_eventually g gi hC hK q hq
  have hent : (fun v => uniformFlowPullbackMetric g gi hC hK q v i j)
      =ᶠ[nhds (0 : Point n)] (fun v => expPullbackMetric g gi hC q v i j) :=
    hB.mono fun v hv => hv i j
  rw [pd_congr_eventuallyEq e hent]
  exact pd_expPullbackMetric_at_zero g gi hC q hgsymm (fun a b => hinvF q a b) hg i j e

/-! ### The center-gauge deviation bounds — `hframeK` replaced by `hdevK`, cost exactly `+ε₀`. -/

/-- **★ Center-gauge FORWARD deviation bound** — `uniformFlowPullbackMetric_dev_uniform` with
    `hframeK` replaced by the frame deviation `hdevK : ∀ q ∈ K, |g(q) − δ| ≤ ε₀`:
    ONE radius `r₀ > 0` and ONE constant `M ≥ 0` (both produced BEFORE `ε₀` — `M` is INDEPENDENT of
    `ε₀`) with `|g̃_q(v)ᵢⱼ − δᵢⱼ| ≤ M·‖v‖² + ε₀` for every `q ∈ K`, `‖v‖ ≤ r₀`.  Proof = the banked
    Taylor replay with the SECOND-order pivot recentred at the true value `g̃_q(0)` (which is `g(q)`,
    not `δ`): `decay_order_two` on `w ↦ g̃(w) − g̃(0)` (value + pd jets at `0`, uniform `C²` packet
    `uniformFlowPullbackMetric_c2_uniform_full`), then the triangle inequality pays `+|g(q) − δ| ≤ ε₀`.
    NOT `a₁ = R/6`. -/
theorem uniformFlowPullbackMetric_dev_uniform_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0) :
    ∃ r₀ > (0 : ℝ), ∃ M : ℝ, 0 ≤ M ∧ ∀ ε₀ : ℝ, 0 ≤ ε₀ →
      (∀ q ∈ K, ∀ i j : Fin n, |g q i j - (if i = j then (1 : ℝ) else 0)| ≤ ε₀) →
      ∀ q ∈ K, ∀ v : Point n, ‖v‖ ≤ r₀ → ∀ i j : Fin n,
        |uniformFlowPullbackMetric g gi hC hK q v i j - (if i = j then (1 : ℝ) else 0)|
          ≤ M * ‖v‖ ^ 2 + ε₀ := by
  obtain ⟨r₀, hr₀0, M, hpk⟩ := uniformFlowPullbackMetric_c2_uniform_full g gi hg hC hK
  refine ⟨r₀ / 2, by positivity, max 0 M, le_max_left _ _, ?_⟩
  intro ε₀ hε₀ hdevK q hq v hv i j
  have hjetpd : ∀ e, pd (fun w => uniformFlowPullbackMetric g gi hC hK q w i j) e
      (0 : Point n) = 0 :=
    fun e => uniformFlowPullbackMetric_pd_zero_center g gi hC hK hg hgsymm hinvF q hq i j e
  set f : Point n → ℝ :=
    fun w => uniformFlowPullbackMetric g gi hC hK q w i j
      - uniformFlowPullbackMetric g gi hC hK q 0 i j with hf
  have hballs : ∀ w : Point n, w ∈ Metric.closedBall (0 : Point n) (r₀ / 2) → ‖w‖ < r₀ := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    linarith
  have hfd_eq : fderiv ℝ f
      = fderiv ℝ (fun w => uniformFlowPullbackMetric g gi hC hK q w i j) := by
    funext w
    exact fderiv_sub_const _
  have hf0 : f 0 = 0 := by rw [hf]; simp
  have h0mem : ‖(0 : Point n)‖ < r₀ := by rw [norm_zero]; exact hr₀0
  have hdf0 : fderiv ℝ f 0 = 0 := by
    rw [hfd_eq]
    exact fderiv_zero_of_pd_zero ((hpk q hq 0 h0mem i j).1.differentiableAt) hjetpd
  have hdiff : ∀ w ∈ Metric.closedBall (0 : Point n) (r₀ / 2), DifferentiableAt ℝ f w := by
    intro w hw
    exact ((hpk q hq w (hballs w hw) i j).1.differentiableAt).sub (differentiableAt_const _)
  have hdiff2 : ∀ w ∈ Metric.closedBall (0 : Point n) (r₀ / 2),
      DifferentiableAt ℝ (fderiv ℝ f) w := by
    intro w hw
    rw [hfd_eq]
    exact (hpk q hq w (hballs w hw) i j).2.1.differentiableAt
  have hbound2 : ∀ w ∈ Metric.closedBall (0 : Point n) (r₀ / 2),
      ‖fderiv ℝ (fderiv ℝ f) w‖ ≤ max 0 M := by
    intro w hw
    rw [hfd_eq]
    exact le_trans (hpk q hq w (hballs w hw) i j).2.2.2.2 (le_max_right _ _)
  have hdecay := decay_order_two f (max 0 M) (r₀ / 2) (by positivity)
    hf0 hdf0 hdiff hdiff2 hbound2 hv
  have hc0dev : |uniformFlowPullbackMetric g gi hC hK q 0 i j
      - (if i = j then (1 : ℝ) else 0)| ≤ ε₀ := by
    rw [uniformFlowPullbackMetric_zero_center g gi hC hK q hq i j]
    exact hdevK q hq i j
  have hsplit : uniformFlowPullbackMetric g gi hC hK q v i j - (if i = j then (1 : ℝ) else 0)
      = f v + (uniformFlowPullbackMetric g gi hC hK q 0 i j
          - (if i = j then (1 : ℝ) else 0)) := by
    simp only [hf]; ring
  rw [hsplit]
  calc |f v + (uniformFlowPullbackMetric g gi hC hK q 0 i j
        - (if i = j then (1 : ℝ) else 0))|
      ≤ |f v| + |uniformFlowPullbackMetric g gi hC hK q 0 i j
          - (if i = j then (1 : ℝ) else 0)| := abs_add_le _ _
    _ ≤ max 0 M * ‖v‖ ^ 2 + ε₀ := add_le_add hdecay hc0dev

/-- **★★ J4-604 capstone — center-gauge INVERSE deviation bound.**  The honest analogue of
    `uniformFlowPullbackMetricInv_dev_uniform` with `hframeK` replaced by
    `hdevK : ∀ q ∈ K, ∀ i j, |g(q)ᵢⱼ − δᵢⱼ| ≤ ε₀`:
    `∃ r₀ > 0, ∃ M ≥ 0, ∀ ε₀ ≥ 0, hdevK → ∀ q ∈ K, ∀ ‖v‖ < r₀, ∀ i j,
        |g̃⁻¹_q(v)ᵢⱼ − δᵢⱼ| ≤ M·(rncRadialSq v + ε₀)`.
    `M` and `r₀` are produced BEFORE `ε₀` (no ε₀-inflation of the packet/Grönwall constants; the
    Neumann push `A⁻¹ − 1 = A⁻¹(1 − A)` is unchanged — `uniformInverseMetric_bound` never used
    `hframeK`).  At `ε₀ = 0` this recovers the banked bound's shape; at the curved witness the
    supplier is `curvedRNC_frame_dev_on_ball`.  NOT `a₁ = R/6`. -/
theorem uniformFlowPullbackMetricInv_dev_uniform_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0) :
    ∃ r₀ > (0 : ℝ), ∃ M : ℝ, 0 ≤ M ∧ ∀ ε₀ : ℝ, 0 ≤ ε₀ →
      (∀ q ∈ K, ∀ i j : Fin n, |g q i j - (if i = j then (1 : ℝ) else 0)| ≤ ε₀) →
      ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ → ∀ i j : Fin n,
        |uniformFlowPullbackMetricInv g gi hC hK q v i j - (if i = j then (1 : ℝ) else 0)|
          ≤ M * (rncRadialSq v + ε₀) := by
  obtain ⟨r₁, hr₁0, Md, hMd0, hdev⟩ :=
    uniformFlowPullbackMetric_dev_uniform_center g gi hC hK hg hgsymm hinvF
  obtain ⟨r₂, hr₂0, Kinv, hinvB⟩ := uniformInverseMetric_bound g gi hg hC hK hgnd
  refine ⟨min r₁ r₂, lt_min hr₁0 hr₂0, max 0 Kinv * (Md + 1),
    mul_nonneg (le_max_left _ _) (by linarith), ?_⟩
  intro ε₀ hε₀ hdevK q hq v hv i j
  have hv1 : ‖v‖ ≤ r₁ := le_of_lt (lt_of_lt_of_le hv (min_le_left _ _))
  have hv2 : ‖v‖ < r₂ := lt_of_lt_of_le hv (min_le_right _ _)
  obtain ⟨hU, hKn, _⟩ := hinvB q hq v hv2
  set A : Point n →L[ℝ] Point n :=
    matToCLM (fun a b => uniformFlowPullbackMetric g gi hC hK q v a b) with hA
  -- entries of `(1 − A)e_j` are the forward-metric deviations.
  have hzk : ∀ k : Fin n, ((1 - A) (Pi.single j (1 : ℝ))) k
      = (if k = j then (1 : ℝ) else 0) - uniformFlowPullbackMetric g gi hC hK q v k j := by
    intro k
    have hAw : (A (Pi.single j (1 : ℝ))) k = uniformFlowPullbackMetric g gi hC hK q v k j := by
      rw [hA, matToCLM_apply]
      simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, Pi.sub_apply, hAw,
      Pi.single_apply]
  have hznorm : ‖(1 - A) (Pi.single j (1 : ℝ))‖ ≤ Md * ‖v‖ ^ 2 + ε₀ := by
    rw [pi_norm_le_iff_of_nonneg (add_nonneg (mul_nonneg hMd0 (sq_nonneg _)) hε₀)]
    intro k
    rw [Real.norm_eq_abs, hzk k, abs_sub_comm]
    exact hdev ε₀ hε₀ hdevK q hq v hv1 k j
  -- the entry deviation IS the `i`-th coordinate of `A⁻¹((1−A)e_j)`.
  have hmain : uniformFlowPullbackMetricInv g gi hC hK q v i j - (if i = j then (1 : ℝ) else 0)
      = ((Ring.inverse A) ((1 - A) (Pi.single j (1 : ℝ)))) i := by
    have hRA : Ring.inverse A ((1 - A) (Pi.single j (1 : ℝ)))
        = Ring.inverse A (Pi.single j (1 : ℝ)) - Pi.single j (1 : ℝ) := by
      have h1 : (1 - A) (Pi.single j (1 : ℝ))
          = Pi.single j (1 : ℝ) - A (Pi.single j (1 : ℝ)) := by
        rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
      have h2 : Ring.inverse A (A (Pi.single j (1 : ℝ))) = Pi.single j (1 : ℝ) := by
        rw [← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel _ hU,
          ContinuousLinearMap.one_apply]
      rw [h1, map_sub, h2]
    rw [hRA, Pi.sub_apply, Pi.single_apply]
    simp only [uniformFlowPullbackMetricInv, hA]
  rw [hmain]
  have hsq : ‖v‖ ^ 2 ≤ rncRadialSq v := by
    rw [← rncRadial_sq]
    nlinarith [norm_le_rncRadial v, norm_nonneg v, rncRadial_nonneg v]
  calc |((Ring.inverse A) ((1 - A) (Pi.single j (1 : ℝ)))) i|
      = ‖((Ring.inverse A) ((1 - A) (Pi.single j (1 : ℝ)))) i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖(Ring.inverse A) ((1 - A) (Pi.single j (1 : ℝ)))‖ := norm_le_pi_norm _ i
    _ ≤ ‖Ring.inverse A‖ * ‖(1 - A) (Pi.single j (1 : ℝ))‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ max 0 Kinv * (Md * ‖v‖ ^ 2 + ε₀) :=
        mul_le_mul (le_trans hKn (le_max_right _ _)) hznorm (norm_nonneg _) (le_max_left _ _)
    _ ≤ max 0 Kinv * (Md + 1) * (rncRadialSq v + ε₀) := by
        have hKm0 : (0 : ℝ) ≤ max 0 Kinv := le_max_left _ _
        have hinner : Md * ‖v‖ ^ 2 + ε₀ ≤ (Md + 1) * (rncRadialSq v + ε₀) := by
          nlinarith [mul_nonneg hMd0 (sub_nonneg.mpr hsq), mul_nonneg hMd0 hε₀,
            rncRadialSq_nonneg v]
        calc max 0 Kinv * (Md * ‖v‖ ^ 2 + ε₀)
            ≤ max 0 Kinv * ((Md + 1) * (rncRadialSq v + ε₀)) :=
              mul_le_mul_of_nonneg_left hinner hKm0
          _ = max 0 Kinv * (Md + 1) * (rncRadialSq v + ε₀) := by ring

/-! ### The fat-`K` curved instantiation — all carries discharged from banked curved lemmas. -/

/-- **The Christoffel smoothness carry for the curved pair** (`hChr` discharged): `christoffel g^κ
    gi^κ` is `C^∞` for `κ ≤ 0`, from the generic `christoffel_contDiff` and the banked
    `curvedRNCMetric_contDiff` / `curvedRNCInv_contDiff`.  NOT `a₁ = R/6`. -/
theorem curvedRNC_hChr (κ : ℝ) (hκ : κ ≤ 0) :
    ∀ a b c : Fin n, ContDiff ℝ (⊤ : WithTop ℕ∞)
      (fun y => christoffel (curvedRNCMetric κ) (curvedRNCInv κ) a b c y) :=
  fun a b c => christoffel_contDiff (curvedRNCMetric κ) (curvedRNCInv κ)
    (fun a' b' => curvedRNCMetric_contDiff κ a' b')
    (fun a' b' => curvedRNCInv_contDiff κ hκ a' b') a b c

/-- **★★ The center-gauge inverse deviation bound AT THE FAT BASE COMPACT for the curved witness.**
    For `κ ≤ 0` and every radius `r`, on `K = Metric.closedBall 0 r`:
    `∃ r₀ > 0, ∃ M ≥ 0, ∀ q ∈ K, ∀ ‖v‖ < r₀, ∀ i j,
        |g̃⁻¹_q(v)ᵢⱼ − δᵢⱼ| ≤ M·(rncRadialSq v + (|κ|/3)·n·r²)`
    — the FIRST member of the J4-603 `hframeK` use-site list
    (`uniformFlowPullbackMetricInv_dev_uniform`) now HOLDS at the fat curved base compact, with
    every carry discharged from banked curved lemmas (`hg` = `curvedRNCMetric_contDiff`, `hgnd` =
    `hgnd_of_hgpos ∘ curvedRNCMetric_hgpos`, `hgsymm` = `curvedRNCMetric_symm`, `hinvF` =
    `curvedRNCMetric_hinvF`, `hChr` = `curvedRNC_hChr`) and the `ε₀`-supplier
    `curvedRNC_frame_dev_on_ball`.  NOT `a₁ = R/6` — the downstream (hbound-fat) layers
    (Christoffel decay, coefficient, residual, producer re-assembly) remain OPEN. -/
theorem curvedRNC_pullbackInv_dev_uniform_center (κ r : ℝ) (hκ : κ ≤ 0) :
    ∃ r₀ > (0 : ℝ), ∃ M : ℝ, 0 ≤ M ∧
      ∀ q ∈ Metric.closedBall (0 : Point n) r, ∀ v : Point n, ‖v‖ < r₀ → ∀ i j : Fin n,
        |uniformFlowPullbackMetricInv (curvedRNCMetric κ) (curvedRNCInv κ) (curvedRNC_hChr κ hκ)
            (isCompact_closedBall (0 : Point n) r) q v i j - (if i = j then (1 : ℝ) else 0)|
          ≤ M * (rncRadialSq v + |κ| / 3 * ((n : ℝ) * r ^ 2)) := by
  obtain ⟨r₀, hr₀0, M, hM0, hmain⟩ :=
    uniformFlowPullbackMetricInv_dev_uniform_center (curvedRNCMetric κ) (curvedRNCInv κ)
      (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r)
      (fun a b => curvedRNCMetric_contDiff κ a b)
      (fun y => hgnd_of_hgpos (curvedRNCMetric κ) (curvedRNCMetric_hgpos κ hκ) y)
      (fun y a b => curvedRNCMetric_symm κ y a b)
      (fun y a b => curvedRNCMetric_hinvF κ hκ y a b)
  exact ⟨r₀, hr₀0, M, hM0,
    hmain (|κ| / 3 * ((n : ℝ) * r ^ 2)) (by positivity) (curvedRNC_frame_dev_on_ball κ r)⟩

/-! ### Non-vacuity gates (the cp466 discipline: antecedent inhabitance, not just conclusion shape). -/

/-- **Non-vacuity of the center gauge at fat `K`.**  At every `r > 0`, `n ≥ 1`: (i) the base compact
    `closedBall 0 r` contains a NONZERO point (the constant vector `r/2` — no `K ⊆ {0}` collapse, in
    contrast to the `hframeK` route killed by `rebased_hframeK_unsat`, J4-603), AND (ii) the
    `hdevK` antecedent of the center-gauge bounds IS satisfied by the curved witness with the
    explicit `ε₀ = (|κ|/3)·n·r²`.  NOT `a₁ = R/6`. -/
theorem curvedRNC_center_gauge_satisfiable (κ r : ℝ) (hr : 0 < r) (hn : 1 ≤ n) :
    (∃ q ∈ Metric.closedBall (0 : Point n) r, q ≠ 0) ∧
      (∀ q ∈ Metric.closedBall (0 : Point n) r, ∀ i j : Fin n,
        |curvedRNCMetric κ q i j - (if i = j then (1 : ℝ) else 0)|
          ≤ |κ| / 3 * ((n : ℝ) * r ^ 2)) := by
  constructor
  · refine ⟨(fun _ => r / 2 : Point n), ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]
      rw [pi_norm_le_iff_of_nonneg (by linarith)]
      intro k
      rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · intro h0
      have hi : (0 : ℕ) < n := hn
      have hcomp := congrFun h0 (⟨0, hi⟩ : Fin n)
      simp only [Pi.zero_apply] at hcomp
      linarith
  · exact curvedRNC_frame_dev_on_ball κ r

/-- **The center-gauge `ε₀` is achievable ARBITRARILY SMALL at fat `K`.**  For every `ε > 0` there is
    `r > 0` with `(|κ|/3)·n·r² < ε` — the frame-deviation floor of the center-gauge bounds shrinks to
    `0` with the base-ball radius while `K = closedBall 0 r` stays fat
    (`curvedRNC_center_gauge_satisfiable`).  Whatever smallness threshold a downstream (hbound-fat)
    layer imposes on `ε₀`, it is reachable.  NOT `a₁ = R/6`. -/
theorem curvedRNC_center_eps_arbitrarily_small (κ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > (0 : ℝ), |κ| / 3 * ((n : ℝ) * r ^ 2) < ε := by
  set C : ℝ := |κ| / 3 * (n : ℝ) with hC
  have hC0 : 0 ≤ C := by positivity
  refine ⟨Real.sqrt (ε / (C + 1)), Real.sqrt_pos.mpr (by positivity), ?_⟩
  have hsq : Real.sqrt (ε / (C + 1)) ^ 2 = ε / (C + 1) := Real.sq_sqrt (by positivity)
  have hgoal : |κ| / 3 * ((n : ℝ) * Real.sqrt (ε / (C + 1)) ^ 2) = C * (ε / (C + 1)) := by
    rw [hsq, hC]; ring
  rw [hgoal]
  have h1 : C / (C + 1) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  calc C * (ε / (C + 1)) = (C / (C + 1)) * ε := by ring
    _ < 1 * ε := mul_lt_mul_of_pos_right h1 hε
    _ = ε := one_mul ε

end QIQTH.CurvedA1CenterAmp
