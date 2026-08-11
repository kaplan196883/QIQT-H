/-
  CurvedA1CenterChr — J4-605: SECOND layer of the (hbound-fat) wall — the CENTER-GAUGE variant of the
  load-bearing Christoffel linear decay `uniformFlowChristoffel_linear_decay`, on the fat base compact
  `K = Metric.closedBall 0 r`, instantiated at the genuinely-curved witness `g^κ = curvedRNCMetric κ`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONESTY FIREWALL.  NOT `a₁ = R/6`; this proves NOTHING about the coefficient.  `a₁ = R/6`
  remains CONDITIONAL (established non-vacuously ONLY for the FLAT tower); the curved re-base still
  owes (hbound-fat) layers 3–5 + fat-`K` `hEmeas` + `hAdom` + `hcont` + the co-instantiated capstone
  application + the prior analytic piles / convergence trio / `hmassone` pre-ρ carriers / `hjets`.
  This brick is the SECOND layer of the (hbound-fat) producer rework, not its closure.

  ── ★★ THE USE-SITE VERDICT (proved by construction, the point of this brick).
  In the banked `UniformCoeffBound.uniformFlowChristoffel_linear_decay` (R2 of J4-87) the frame
  normalisation `hframeK : ∀ q ∈ K, g q = δ` enters through EXACTLY ONE inner call: the pd-linear-decay
  layer R1 (`uniformFlowPullbackMetric_pd_linear_decay`), which invokes
  `uniformFlowPullbackMetric_jet_zero … (hframeK q hq)` and then DISCARDS the value jet — only the
  pd-jet `∂g̃_q(0) = 0` is consumed (`⟨_, hjetpd⟩`).  The other pillar of R2, the uniform inverse
  entry bound `uniformFlowPullbackMetricInv_entry_uniform_bound`, never takes `hframeK` at all.
  Since J4-604 proved the pd-jet FRAME-FREE (`uniformFlowPullbackMetric_pd_zero_center` — RNC
  radiality kills `∂g̃(0)` at EVERY base point, δ-frame or not), the center-gauge Christoffel decay
  survives with the decay form UNCHANGED AND NO `ε₀` TERM AT ALL:
      `|Γ̃^k_ij(v)| ≤ KdΓ · ‖v‖`,   KdΓ = ½·n·Kg·3·Kpd,   uniform over `q ∈ K`,
  where `Kg` (inverse entry bound) and `Kpd` (pd decay) are both produced by frame-free machinery.
  `hframeK` is not WEAKENED here — it is REMOVED.  The `g̃⁻¹` factor in `Γ = ½g̃⁻¹(∂g̃+∂g̃−∂g̃)`
  needs only BOUNDEDNESS (`Kg`), not proximity to `δ`, and `∂g̃(0) = 0` holds frame-free, so the
  0th-order term vanishes regardless of the frame at `q`.  NO silent `ε₀` was dropped: there is
  genuinely no `ε₀` in this layer (contrast layer 1, where the VALUE jet `g̃(0) = g(q)` forces `+ε₀`).

  ── LANDED HERE (all frame-free, i.e. WITHOUT `hframeK`):
    • `uniformFlowPullbackMetric_pd_linear_decay_center` — R1 replay: `|∂g̃(v)| ≤ Kpd·‖v‖` uniform
      over `K`, pd-jet from `uniformFlowPullbackMetric_pd_zero_center` (J4-604) instead of
      `uniformFlowPullbackMetric_jet_zero`+`hframeK`.
    • `uniformFlowChristoffel_zero_at_zero_center` — `Γ̃_q(0) = 0` at EVERY `q ∈ K`, frame-free
      (feeds layer 3 where the banked file used the framed `uniformFlowChristoffel_zero_at_zero`).
    • `uniformFlowChristoffel_linear_decay_center` — ★ THE BRICK: R2 replay, `hframeK` deleted,
      same constant assembly `KdΓ = ½·n·Kg·(3·Kpd)`.
    • `curvedRNC_Chr_linear_decay_center` — ★★ fat-`K` curved instantiation: for `κ ≤ 0` and EVERY
      radius `r`, on `K = closedBall 0 r` the decay holds at the curved witness, all carries
      discharged from banked curved lemmas (`curvedRNCMetric_contDiff`, `hgnd_of_hgpos ∘
      curvedRNCMetric_hgpos`, `curvedRNCMetric_symm`, `curvedRNCMetric_hinvF`, `curvedRNC_hChr`).
    • `curvedRNC_Chr_center_satisfiable` — non-vacuity gate (cp466 discipline): at every `r > 0`,
      `n ≥ 1` the base compact contains a NONZERO point (no `K ⊆ {0}` collapse — contrast
      `rebased_hframeK_unsat`, J4-603) AND the decay conclusion is INHABITED there; the theorem has
      no `hdevK`/`ε₀` antecedent left to gate.

  ── REMAINING (hbound-fat) LAYERS (scoped, OPEN — in dependency order):
    3. center-gauge `uniformCoeff_bound` / `uniformCoeffLinear_bound` (consumes layers 1+2; the `ε₀`
       from layer 1's inverse-deviation bound WILL surface there through the `coeffAF` diagonal trace),
    4. center-gauge `uniformResidual(_Linear)_gaussian_bound_tau_narrow`,
    5. producer re-assembly (`cutoffResidualN1_uniformFlow_narrow_mixed_below_lin` →
       `gatedWitnessN1_hEboundW_le_lin_CONST` → fat-`K` dom pkg) with `ε₀` tracked through the
       width-2 Gaussian bookkeeping.

  No `sorry`, no `admit`, no new axioms, no `:= True`, no vacuous antecedent posing as a discharge;
  no existing file edited except the `QIQTH.lean` / `AxiomAudit.lean` wiring; nothing committed.
-/
import Mathlib
import QIQTH.UniformFlowJetZero
import QIQTH.UniformFlowMetricInvProps
import QIQTH.CurvedA1CenterAmp
import QIQTH.CurvedRNCGaugeBundle
import QIQTH.CurvedRNCPosDef
import QIQTH.OuterCarryRecon
import QIQTH.ChristoffelSmooth

open QIQTH.Curvature QIQTH.PullbackMetric QIQTH.RadialDistance QIQTH.RNCDecay
open QIQTH.ExpMap QIQTH.CurvedRNCGaussWitness QIQTH.CurvedRNCGaugeBundle
open QIQTH.CurvedRNCPosDef QIQTH.OuterCarryRecon QIQTH.CurvedA1CenterAmp
open Set Filter
open scoped Topology BigOperators

namespace QIQTH.CurvedA1CenterChr

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ### R1, center gauge — uniform `|∂g̃(v)| ≤ Kpd·‖v‖` WITHOUT the frame hypothesis. -/

/-- **★ Center-gauge R1 — uniform `|∂g̃(v)| ≤ Kpd·‖v‖`, FRAME-FREE.**  The banked
    `uniformFlowPullbackMetric_pd_linear_decay` used `hframeK` solely to feed
    `uniformFlowPullbackMetric_jet_zero`, of which only the pd-jet component was consumed.  The
    pd-jet is frame-free (`uniformFlowPullbackMetric_pd_zero_center`, J4-604 — RNC radiality), so
    the mean-value replay (`fderiv_zero_of_pd_zero` + `fderiv_decay` on the uniform `C²` packet
    `uniformFlowPullbackMetric_c2_uniform_full`) goes through with `hframeK` DELETED and the decay
    form UNCHANGED — no `ε₀` enters this layer.  NOT `a₁ = R/6`. -/
theorem uniformFlowPullbackMetric_pd_linear_decay_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0) :
    ∃ r > (0 : ℝ), ∃ Kpd : ℝ, 0 ≤ Kpd ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r → ∀ a b e : Fin n,
      |pd (fun y => uniformFlowPullbackMetric g gi hC hK q y a b) e v| ≤ Kpd * ‖v‖ := by
  obtain ⟨r₀, hr₀0, M, hpk⟩ := uniformFlowPullbackMetric_c2_uniform_full g gi hg hC hK
  refine ⟨r₀ / 2, by positivity, max 0 M, le_max_left _ _, ?_⟩
  intro q hq v hv a b e
  -- the FRAME-FREE pd-jet (J4-604): `∂g̃_q(0) = 0` with no frame normalisation at `q`.
  have hjetpd : ∀ e' : Fin n,
      pd (fun y => uniformFlowPullbackMetric g gi hC hK q y a b) e' (0 : Point n) = 0 :=
    fun e' => uniformFlowPullbackMetric_pd_zero_center g gi hC hK hg hgsymm hinvF q hq a b e'
  set f : Point n → ℝ := fun w => uniformFlowPullbackMetric g gi hC hK q w a b with hfdef
  have hballs : ∀ w : Point n, w ∈ Metric.closedBall (0 : Point n) (r₀ / 2) → ‖w‖ < r₀ := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right] at hw
    linarith
  have h0mem : ‖(0 : Point n)‖ < r₀ := by rw [norm_zero]; exact hr₀0
  -- `fderiv f 0 = 0` from vanishing partials + differentiability at `0`.
  have hdf0 : fderiv ℝ f 0 = 0 :=
    fderiv_zero_of_pd_zero ((hpk q hq 0 h0mem a b).1.differentiableAt) (fun e' => hjetpd e')
  -- second-layer differentiability + bound on the closed half-ball.
  have hdiff2 : ∀ w ∈ Metric.closedBall (0 : Point n) (r₀ / 2),
      DifferentiableAt ℝ (fderiv ℝ f) w :=
    fun w hw => (hpk q hq w (hballs w hw) a b).2.1.differentiableAt
  have hbound2 : ∀ w ∈ Metric.closedBall (0 : Point n) (r₀ / 2),
      ‖fderiv ℝ (fderiv ℝ f) w‖ ≤ max 0 M :=
    fun w hw => le_trans (hpk q hq w (hballs w hw) a b).2.2.2.2 (le_max_right _ _)
  have hvmem : v ∈ Metric.closedBall (0 : Point n) (r₀ / 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hv.le
  have hgrad := fderiv_decay f (max 0 M) (r₀ / 2) (by positivity) hdf0 hdiff2 hbound2 hvmem
  have hdiffAt : DifferentiableAt ℝ f v := (hpk q hq v (hballs v hvmem) a b).1.differentiableAt
  rw [pd_eq_fderiv f e v hdiffAt]
  calc |fderiv ℝ f v (Pi.single e 1)|
      = ‖fderiv ℝ f v (Pi.single e (1 : ℝ))‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ f v‖ * ‖(Pi.single e (1 : ℝ) : Point n)‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ f v‖ * 1 := by rw [Pi.norm_single, norm_one]
    _ = ‖fderiv ℝ f v‖ := mul_one _
    _ ≤ max 0 M * ‖v‖ := hgrad

/-! ### `Γ̃_q(0) = 0`, FRAME-FREE (feeds layer 3). -/

/-- **Center-gauge `Γ̃_q(0) = 0`, frame-free.**  At the RNC centre the Christoffel symbols of the
    uniform-flow pullback metric vanish at EVERY `q ∈ K` with NO frame normalisation, because each
    `∂g̃_q(0) = 0` frame-free (`uniformFlowPullbackMetric_pd_zero_center`, J4-604) and
    `Γ̃ = ½g̃⁻¹(∂g̃+∂g̃−∂g̃)`.  Replaces the framed `uniformFlowChristoffel_zero_at_zero` for the
    downstream center-gauge layers.  NOT `a₁ = R/6`. -/
theorem uniformFlowChristoffel_zero_at_zero_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0)
    (q : Point n) (hq : q ∈ K) (k i j : Fin n) :
    christoffel (fun w a b => uniformFlowPullbackMetric g gi hC hK q w a b)
        (fun w a b => uniformFlowPullbackMetricInv g gi hC hK q w a b) k i j (0 : Point n) = 0 := by
  have hjetpd : ∀ a b e : Fin n,
      pd (fun y => uniformFlowPullbackMetric g gi hC hK q y a b) e (0 : Point n) = 0 :=
    fun a b e => uniformFlowPullbackMetric_pd_zero_center g gi hC hK hg hgsymm hinvF q hq a b e
  simp only [christoffel]
  rw [show (∑ α, uniformFlowPullbackMetricInv g gi hC hK q 0 k α
        * (pd (fun y => uniformFlowPullbackMetric g gi hC hK q y α j) i 0
            + pd (fun y => uniformFlowPullbackMetric g gi hC hK q y α i) j 0
            - pd (fun y => uniformFlowPullbackMetric g gi hC hK q y i j) α 0)) = 0 from ?_]
  · ring
  · refine Finset.sum_eq_zero fun α _ => ?_
    rw [hjetpd α j i, hjetpd α i j, hjetpd i j α]; ring

/-! ### R2, center gauge — ★ THE BRICK: the Christoffel linear decay, FRAME-FREE. -/

/-- **★★ J4-605 — CENTER-GAUGE CHRISTOFFEL LINEAR DECAY, uniform over `K`, FRAME-FREE.**
    `|Γ̃^k_ij(v)| ≤ KdΓ·‖v‖` for every `q ∈ K`, `‖v‖ < r₀`, with `KdΓ = ½·n·Kg·(3·Kpd)` — the SAME
    decay form and the SAME constant assembly as the banked `uniformFlowChristoffel_linear_decay`,
    but with `hframeK` DELETED (not weakened to `hdevK`): the inverse entry bound
    `uniformFlowPullbackMetricInv_entry_uniform_bound` never used the frame, and the pd decay is the
    frame-free center replay (R1 above).  NO `ε₀` appears — the honest verdict of the use-site map:
    `hframeK` entered R2 only through the pd-jet, which RNC radiality supplies at every base point.
    Hypotheses ONLY `hg`+`hC`+`IsCompact K`+`hgnd`+`hgsymm`+`hinvF`, all genuine; NOT `a₁ = R/6`. -/
theorem uniformFlowChristoffel_linear_decay_center (g gi : Point n → Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K)
    (hgnd : ∀ y : Point n, IsUnit (matToCLM (fun a b => g y a b)))
    (hgsymm : ∀ y a b, g y a b = g y b a)
    (hinvF : ∀ y a b, (∑ σ, g y a σ * gi y σ b) = if a = b then 1 else 0) :
    ∃ r₀ > (0 : ℝ), ∃ KdΓ : ℝ, 0 ≤ KdΓ ∧ ∀ q ∈ K, ∀ v : Point n, ‖v‖ < r₀ → ∀ k i j : Fin n,
      |christoffel (fun w a b => uniformFlowPullbackMetric g gi hC hK q w a b)
          (fun w a b => uniformFlowPullbackMetricInv g gi hC hK q w a b) k i j v|
        ≤ KdΓ * ‖v‖ := by
  obtain ⟨r₁, hr₁0, Kg, hKg0, hGIb⟩ :=
    uniformFlowPullbackMetricInv_entry_uniform_bound g gi hg hC hK hgnd
  obtain ⟨r₂, hr₂0, Kpd, hKpd0, hpdb⟩ :=
    uniformFlowPullbackMetric_pd_linear_decay_center g gi hg hC hK hgsymm hinvF
  refine ⟨min r₁ r₂, lt_min hr₁0 hr₂0,
    (1 / 2) * (n : ℝ) * Kg * (3 * Kpd), by positivity, ?_⟩
  intro q hq v hv k i j
  have hv1 : ‖v‖ < r₁ := lt_of_lt_of_le hv (min_le_left _ _)
  have hv2 : ‖v‖ < r₂ := lt_of_lt_of_le hv (min_le_right _ _)
  have hGI : ∀ a b : Fin n, |uniformFlowPullbackMetricInv g gi hC hK q v a b| ≤ Kg :=
    fun a b => hGIb q hq v hv1 a b
  have hpd : ∀ a b e : Fin n,
      |pd (fun y => uniformFlowPullbackMetric g gi hC hK q y a b) e v| ≤ Kpd * ‖v‖ :=
    fun a b e => hpdb q hq v hv2 a b e
  -- per-α term bound.
  have hterm : ∀ α : Fin n,
      |uniformFlowPullbackMetricInv g gi hC hK q v k α
          * (pd (fun y => uniformFlowPullbackMetric g gi hC hK q y α j) i v
            + pd (fun y => uniformFlowPullbackMetric g gi hC hK q y α i) j v
            - pd (fun y => uniformFlowPullbackMetric g gi hC hK q y i j) α v)|
        ≤ Kg * (3 * (Kpd * ‖v‖)) := by
    intro α
    rw [abs_mul]
    set A := pd (fun y => uniformFlowPullbackMetric g gi hC hK q y α j) i v with hAdef
    set B := pd (fun y => uniformFlowPullbackMetric g gi hC hK q y α i) j v with hBdef
    set C := pd (fun y => uniformFlowPullbackMetric g gi hC hK q y i j) α v with hCdef
    have h2 : |A + B - C| ≤ 3 * (Kpd * ‖v‖) := by
      have htri := abs_add_le (A + B) (-C)
      rw [← sub_eq_add_neg, abs_neg] at htri
      have hle : |A + B - C| ≤ |A| + |B| + |C| :=
        le_trans htri (by gcongr; exact abs_add_le _ _)
      calc |A + B - C| ≤ |A| + |B| + |C| := hle
        _ ≤ Kpd * ‖v‖ + Kpd * ‖v‖ + Kpd * ‖v‖ := by
            gcongr
            · exact hpd α j i
            · exact hpd α i j
            · exact hpd i j α
        _ = 3 * (Kpd * ‖v‖) := by ring
    exact mul_le_mul (hGI k α) h2 (abs_nonneg _) hKg0
  -- assemble.
  simp only [christoffel]
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc (1 / 2 : ℝ)
        * |∑ α, uniformFlowPullbackMetricInv g gi hC hK q v k α
            * (pd (fun y => uniformFlowPullbackMetric g gi hC hK q y α j) i v
              + pd (fun y => uniformFlowPullbackMetric g gi hC hK q y α i) j v
              - pd (fun y => uniformFlowPullbackMetric g gi hC hK q y i j) α v)|
      ≤ (1 / 2 : ℝ) * ∑ α, Kg * (3 * (Kpd * ‖v‖)) := by
        gcongr
        exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun α _ => hterm α)
    _ = (1 / 2 : ℝ) * (n : ℝ) * Kg * (3 * Kpd) * ‖v‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-! ### The fat-`K` curved instantiation — all carries discharged from banked curved lemmas. -/

/-- **★★ THE CHRISTOFFEL LINEAR DECAY AT THE FAT BASE COMPACT for the curved witness.**  For `κ ≤ 0`
    and EVERY radius `r`, on `K = Metric.closedBall 0 r`:
    `∃ r₀ > 0, ∃ KdΓ ≥ 0, ∀ q ∈ K, ∀ ‖v‖ < r₀, ∀ k i j, |Γ̃_q^k_ij(v)| ≤ KdΓ·‖v‖`
    — the SECOND member of the (hbound-fat) `hframeK` use-site list
    (`uniformFlowChristoffel_linear_decay`) now HOLDS at the fat curved base compact, with every
    carry discharged from banked curved lemmas (`hg` = `curvedRNCMetric_contDiff`, `hgnd` =
    `hgnd_of_hgpos ∘ curvedRNCMetric_hgpos`, `hgsymm` = `curvedRNCMetric_symm`, `hinvF` =
    `curvedRNCMetric_hinvF`, `hChr` = `curvedRNC_hChr`) and NO frame or deviation hypothesis at all.
    NOT `a₁ = R/6` — the downstream (hbound-fat) layers (coefficient, residual, producer
    re-assembly) remain OPEN. -/
theorem curvedRNC_Chr_linear_decay_center (κ r : ℝ) (hκ : κ ≤ 0) :
    ∃ r₀ > (0 : ℝ), ∃ KdΓ : ℝ, 0 ≤ KdΓ ∧
      ∀ q ∈ Metric.closedBall (0 : Point n) r, ∀ v : Point n, ‖v‖ < r₀ → ∀ k i j : Fin n,
        |christoffel
            (fun w a b => uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r) q w a b)
            (fun w a b => uniformFlowPullbackMetricInv (curvedRNCMetric κ) (curvedRNCInv κ)
              (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r) q w a b)
            k i j v|
          ≤ KdΓ * ‖v‖ :=
  uniformFlowChristoffel_linear_decay_center (curvedRNCMetric κ) (curvedRNCInv κ)
    (fun a b => curvedRNCMetric_contDiff κ a b)
    (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r)
    (fun y => hgnd_of_hgpos (curvedRNCMetric κ) (curvedRNCMetric_hgpos κ hκ) y)
    (fun y a b => curvedRNCMetric_symm κ y a b)
    (fun y a b => curvedRNCMetric_hinvF κ hκ y a b)

/-! ### Non-vacuity gate (the cp466 discipline: antecedent inhabitance, not just conclusion shape). -/

/-- **Non-vacuity of the center-gauge Christoffel decay at fat `K`.**  At every `r > 0`, `n ≥ 1`,
    `κ ≤ 0`: (i) the base compact `closedBall 0 r` contains a NONZERO point (no `K ⊆ {0}` collapse —
    contrast `rebased_hframeK_unsat`, J4-603), AND (ii) the decay conclusion is INHABITED there —
    i.e. `curvedRNC_Chr_linear_decay_center` produces its radius/constant with the fat compact as
    stated.  Note the theorem has NO `hdevK`/`ε₀`/frame antecedent left to gate: every hypothesis of
    `uniformFlowChristoffel_linear_decay_center` was discharged by a banked curved lemma, so the
    only vacuity channel is `K`-collapse, excluded by (i).  NOT `a₁ = R/6`. -/
theorem curvedRNC_Chr_center_satisfiable (κ r : ℝ) (hκ : κ ≤ 0) (hr : 0 < r) (hn : 1 ≤ n) :
    (∃ q ∈ Metric.closedBall (0 : Point n) r, q ≠ 0) ∧
      (∃ r₀ > (0 : ℝ), ∃ KdΓ : ℝ, 0 ≤ KdΓ ∧
        ∀ q ∈ Metric.closedBall (0 : Point n) r, ∀ v : Point n, ‖v‖ < r₀ → ∀ k i j : Fin n,
          |christoffel
              (fun w a b => uniformFlowPullbackMetric (curvedRNCMetric κ) (curvedRNCInv κ)
                (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r) q w a b)
              (fun w a b => uniformFlowPullbackMetricInv (curvedRNCMetric κ) (curvedRNCInv κ)
                (curvedRNC_hChr κ hκ) (isCompact_closedBall (0 : Point n) r) q w a b)
              k i j v|
            ≤ KdΓ * ‖v‖) :=
  ⟨(curvedRNC_center_gauge_satisfiable κ r hr hn).1,
    curvedRNC_Chr_linear_decay_center κ r hκ⟩

end QIQTH.CurvedA1CenterChr
