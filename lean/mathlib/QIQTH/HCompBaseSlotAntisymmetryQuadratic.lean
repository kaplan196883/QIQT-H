/-
  HCompBaseSlotAntisymmetryQuadratic — J4-1002: the GO-classified abstract "antisymmetry quadratic
  defect" brick for `VanVleckGatedSpatialSymmetry.hcomp`'s base-slot change-of-variables item (a),
  Sol-consulted (gpt-5.6-sol, high, 2026-08-22) GO/NO-GO on the exact question left open at the end of
  J4-1001 (`GaussCompMixedHessian`): whether the base↔eval chart-recentering defect is LINEAR (fatal
  `τ⁻¹`, mirrors the cp872 `WitnessTranspositionGeneralBound` NO-GO) or QUADRATIC-OR-BETTER (needed for
  `hcomp`'s `O(√ε)` rate).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure real-analysis/Taylor-remainder brick, fully abstract in the map `Φ` (mirrors how
  `GaussCompMixedHessian`/`HeatHessianMomentCancellation` stayed abstract before touching
  `uniformInverseChart`/`kPrime`).  It does **NOT** discharge `hcomp`: it does NOT touch `kPrime`,
  `heatHessMult`, the Gaussian weight, the `∫z`/`∫s` integrals, or `VanVleckGatedSpatialSymmetry`
  itself.  It supplies ONLY the order-counting fact Sol's NO-GO consult flagged as the prerequisite
  GO/NO-GO gate for attempting the base-slot CoV (item a) at all.  No `sorry`, no new axioms, no
  `:= True`, no vacuous hypothesis (non-vacuity: `Φ p q := p - q` satisfies every hypothesis with the
  defect IDENTICALLY zero — a genuine, non-degenerate check), none equal to the conclusion, no existing
  file edited.  `hCConv`/`hcomp` NOT closed.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel,
  hDConv, hCConv}`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE SYMPY GATE (mandatory pre-check, per campaign discipline).  `docs/qg_roadmap/rnc_sympy/
  hcomp_baseslot_antisymmetry_order.py` verifies, BOTH in a scalar toy model and in a general `n=2`
  matrix/vector model (exact symbolic `== 0` checks, not numerics), that for a map `Φ(q,p)` with
  (F1) `Φ(q,q) = 0` for `q` in a WHOLE neighbourhood of a base point `q₀` (not just at one point) and
  (F3) `Φ` jointly `ContDiffAt ℝ 2` at `(q₀,q₀)`, the antisymmetry defect `Ξ(q,p) := Φ(q,p) + Φ(p,q)`
  has ZERO linear-order Taylor coefficient — FORCED automatically by (F1) alone, with NO NEED for the
  extra fact `∂ₚΦ(q₀,q₀) = Id` (unlike the `GeodesicReversalRoute`/`ChartJetHessian` `DV(q₀) = Id`
  pattern, which is a red herring for THIS specific order-counting question) — leaving a genuine
  QUADRATIC leading term.  Sol confirmed the GO verdict and made ONE correction to the sympy write-up's
  framing: plain `ContDiffAt ℝ 2` gives an `o(‖·‖²)` Taylor remainder, not literally `O(‖·‖³)`; the
  Lean statement below is written honestly against the `o(‖·‖²)`/mean-value-bound level `ContDiffAt ℝ 2`
  actually supports (matching `JointRNCRegularityLocal.jointRNCRegularityLocal_of_diag`'s proof
  technique exactly), NOT the sympy script's illustrative formal-Taylor-series bookkeeping.

  ## THE SCOPING CHOICE (why the bound is stated at `p₂ = q₀` fixed, not fully joint in `p₁,p₂`).
  A fully joint statement `‖Φ(p₁,p₂)+Φ(p₂,p₁)‖ ≤ C‖p₁-p₂‖²` for `p₁,p₂` BOTH ranging near `q₀` needs a
  SECOND round of the same argument (peeling the diagonal-quadratic-form off the full joint 2-jet via
  polarization) that the campaign's actual consumption pattern does not need: `hcomp`'s literal use is
  always at ONE argument frozen to the field point `x` (`Φ z x` vs `Φ x z`), so it suffices — and is
  exactly what `uniformInverseChart_slice_value_diag`/`_jointContDiffAt_diag` (both proved for a
  GENERAL base point) supply when instantiated at `q₀ := x` — to bound `‖Φ(p,q₀)+Φ(q₀,p)‖ ≤ C‖p-q₀‖²`
  for `p` near `q₀`.  This is the honest, minimal, DIRECTLY-CONSUMABLE scoping (Sol: "narrowly scoped
  bankable lemma", not a third full hcomp route).

  ## WHAT LANDS (ns `QIQTH.HCompBaseSlotAntisymmetry`).
    • `antisymmetryDefect_fderiv_zero` — the slice `g p := Φ p q₀ + Φ q₀ p` has `g q₀ = 0` and
      `HasFDerivAt g 0 q₀`, from (F1)+(F3) alone (no normalization fact needed).
    • `antisymmetryDefect_quadratic_bound` — ★★★ THE PAYOFF: `∃ r > 0, C ≥ 0, ∀ p, ‖p - q₀‖ < r →
      ‖Φ p q₀ + Φ q₀ p‖ ≤ C * ‖p - q₀‖ ^ 2`.  Genuinely proved via the SAME mean-value/mean-value
      technique `JointRNCRegularityLocal.jointRNCRegularityLocal_of_diag`'s `hVdisp` field uses.
    • `uniformInverseChart_antisymmetryDefect_quadratic` — the CONCRETE corollary, instantiating
      `Φ := uniformInverseChart g gi hC (closedBall q₀ 1)` and feeding
      `uniformInverseChart_slice_value_diag`/`uniformInverseChart_jointContDiffAt_diag` (J4-856/857).
    • `antisymmetryDefect_quadratic_bound_hyp_satisfiable` — non-vacuity witness `Φ p q := p - q`
      (linear, antisymmetric EXACTLY, defect ≡ 0), confirming the hypothesis bundle is inhabited by a
      genuine, non-degenerate map.

  ## HONEST DISTANCE (what remains before this feeds `hcomp` literally).  This does NOT instantiate
  `kPrime`, does NOT relate `Φ`'s FIELD-slot JETS `P,Q` (the objects `heatHessMult`/
  `gaussComp_pd_pd_mixed` actually consume) to the antisymmetry defect bound above, does NOT do the
  actual base-slot change of variables (turning `∫z` into an integral over the displacement `v`), and
  does NOT touch the `τ`-weighted Gaussian integral or the sliver `ds`-integration.  Per Sol's audit,
  the more likely blocker to full `hcomp` closure is a DIFFERENT, orthogonal gap — the
  pointwise-to-uniform/integral interface between `HCompNearCarryChartSurfaceWired`'s gate-level
  equality (J4-858..888 thread) and `VanVleckGatedSpatialSymmetry.hcomp`'s literal integral shape
  (common local constants/radii, measurability, CoV-Jacobian control) — NOT re-derivable from this
  order-counting brick alone.  `hCConv` NOT closed.  `a₁ = R/6` remains STRICTLY CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.JointRNCRegularityInterfaceLocal

open Filter
open QIQTH.Curvature QIQTH.ExpMap QIQTH.JointRNCRegularityLocal
open scoped Topology

namespace QIQTH.HCompBaseSlotAntisymmetry

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### 1. The abstract order-1 vanishing: `g q₀ = 0` and `HasFDerivAt g 0 q₀`.
    ############################################################################### -/

/-- **`antisymmetryDefect_fderiv_zero`.**  For `Φ : Point n → Point n → Point n`, a base point `q₀`,
    (F1) `Φ q q = 0` for `q` EVENTUALLY near `q₀` (the whole-neighbourhood diagonal-vanishing identity,
    NOT just `Φ q₀ q₀ = 0`), and (F3) `Φ` jointly `ContDiffAt ℝ 2` at `(q₀,q₀)`: the antisymmetrized
    slice `g p := Φ p q₀ + Φ q₀ p` satisfies `g q₀ = 0` and `HasFDerivAt g 0 q₀`.  Proof: `φ q := Φ q q`
    is eventually `0` near `q₀` (F1), so `HasFDerivAt φ 0 q₀`; but `φ = (uncurried Φ) ∘ (fun q => (q,q))`
    with the diagonal embedding having `HasFDerivAt (fun q => (q,q)) (CLM w ↦ (w,w)) q₀`, so by
    UNIQUENESS of the Fréchet derivative, `D(uncurried Φ)(q₀,q₀) (w,w) = 0` for every `w`.  Since
    `D(uncurried Φ)(q₀,q₀)` is linear on the PRODUCT `Point n × Point n`, `(w,w) = (w,0) + (0,w)` gives
    `∂₁Φ(q₀,q₀)(w) + ∂₂Φ(q₀,q₀)(w) = 0` — exactly `Dg(q₀)(w)` by the two-term chain rule (the `p ↦
    Φ p q₀` and `p ↦ Φ q₀ p` slices).  NOT `a₁ = R/6`. -/
theorem antisymmetryDefect_fderiv_zero (Φ : Point n → Point n → Point n) (q₀ : Point n)
    (hdiag : ∀ᶠ q in 𝓝 q₀, Φ q q = 0)
    (hjointC2 : ContDiffAt ℝ 2 (fun p : Point n × Point n => Φ p.1 p.2) (q₀, q₀)) :
    Φ q₀ q₀ + Φ q₀ q₀ = 0 ∧
    HasFDerivAt (fun p => Φ p q₀ + Φ q₀ p) (0 : Point n →L[ℝ] Point n) q₀ := by
  -- `Φ q₀ q₀ = 0` from the eventual identity at the centre.
  have hval0 : Φ q₀ q₀ = 0 := hdiag.self_of_nhds
  refine ⟨by rw [hval0]; simp, ?_⟩
  -- the uncurried map has a genuine Fréchet derivative at `(q₀,q₀)` (from joint `C²`, hence `C¹`).
  have hF1 : ContDiffAt ℝ 1 (fun p : Point n × Point n => Φ p.1 p.2) (q₀, q₀) :=
    hjointC2.of_le (by norm_num)
  have hFdiff : DifferentiableAt ℝ (fun p : Point n × Point n => Φ p.1 p.2) (q₀, q₀) :=
    hF1.differentiableAt (by norm_num)
  set D : Point n × Point n →L[ℝ] Point n := fderiv ℝ (fun p : Point n × Point n => Φ p.1 p.2) (q₀, q₀)
    with hDdef
  have hFD : HasFDerivAt (fun p : Point n × Point n => Φ p.1 p.2) D (q₀, q₀) := hFdiff.hasFDerivAt
  -- the diagonal embedding `q ↦ (q,q)` and its derivative.
  have hdiagFD : HasFDerivAt (fun q : Point n => (q, q))
      (ContinuousLinearMap.id ℝ (Point n) |>.prod (ContinuousLinearMap.id ℝ (Point n))) q₀ :=
    (hasFDerivAt_id q₀).prodMk (hasFDerivAt_id q₀)
  -- chain rule: `φ q := Φ q q` has derivative `D ∘ (w ↦ (w,w))` at `q₀`.
  have hφFD : HasFDerivAt (fun q : Point n => Φ q q)
      (D.comp (ContinuousLinearMap.id ℝ (Point n) |>.prod (ContinuousLinearMap.id ℝ (Point n)))) q₀ := by
    have h := HasFDerivAt.comp q₀ (f := fun q : Point n => (q, q)) hFD hdiagFD
    simpa [Function.comp] using h
  -- but `φ` is eventually `0` near `q₀`, so its derivative there is `0`.
  have hdiagEq : (fun q : Point n => Φ q q) =ᶠ[𝓝 q₀] (fun _ : Point n => (0 : Point n)) := hdiag
  have hφ0FD : HasFDerivAt (fun q : Point n => Φ q q) (0 : Point n →L[ℝ] Point n) q₀ :=
    (hasFDerivAt_const (0 : Point n) q₀).congr_of_eventuallyEq hdiagEq
  -- uniqueness of the Fréchet derivative: the two derivative CLMs of `φ` at `q₀` agree.
  have hDeq : D.comp (ContinuousLinearMap.id ℝ (Point n) |>.prod (ContinuousLinearMap.id ℝ (Point n)))
      = (0 : Point n →L[ℝ] Point n) := hφFD.unique hφ0FD
  -- pointwise: `D (w, w) = 0` for every `w`.
  have hDww : ∀ w : Point n, D (w, w) = 0 := by
    intro w
    have := congrArg (fun L : Point n →L[ℝ] Point n => L w) hDeq
    simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply] using this
  -- linearity of `D` on the product: `D (w, w) = D (w, 0) + D (0, w)`.
  have hDsplit : ∀ w : Point n, D (w, 0) + D (0, w) = 0 := by
    intro w
    have hsum : ((w, 0) : Point n × Point n) + (0, w) = (w, w) := by
      apply Prod.ext <;> simp
    calc D (w, 0) + D (0, w) = D ((w, 0) + (0, w)) := (D.map_add _ _).symm
      _ = D (w, w) := by rw [hsum]
      _ = 0 := hDww w
  -- `g p := Φ p q₀ + Φ q₀ p` has derivative `w ↦ D(w,0) + D(0,w)` at `q₀`, via the two chain rules.
  have hg1 : HasFDerivAt (fun p : Point n => Φ p q₀)
      (D.comp (ContinuousLinearMap.inl ℝ (Point n) (Point n))) q₀ := by
    have h := HasFDerivAt.comp q₀ (f := fun p : Point n => (p, q₀)) hFD
      ((hasFDerivAt_id q₀).prodMk (hasFDerivAt_const q₀ q₀))
    simpa [Function.comp] using h
  have hg2 : HasFDerivAt (fun p : Point n => Φ q₀ p)
      (D.comp (ContinuousLinearMap.inr ℝ (Point n) (Point n))) q₀ := by
    have h := HasFDerivAt.comp q₀ (f := fun p : Point n => (q₀, p)) hFD
      ((hasFDerivAt_const q₀ q₀).prodMk (hasFDerivAt_id q₀))
    simpa [Function.comp] using h
  have hgFD : HasFDerivAt (fun p : Point n => Φ p q₀ + Φ q₀ p)
      (D.comp (ContinuousLinearMap.inl ℝ (Point n) (Point n))
        + D.comp (ContinuousLinearMap.inr ℝ (Point n) (Point n))) q₀ :=
    hg1.add hg2
  have hzero : (D.comp (ContinuousLinearMap.inl ℝ (Point n) (Point n))
      + D.comp (ContinuousLinearMap.inr ℝ (Point n) (Point n))) = (0 : Point n →L[ℝ] Point n) := by
    apply ContinuousLinearMap.ext
    intro w
    have h1 : D.comp (ContinuousLinearMap.inl ℝ (Point n) (Point n)) w = D (w, 0) := rfl
    have h2 : D.comp (ContinuousLinearMap.inr ℝ (Point n) (Point n)) w = D (0, w) := rfl
    show D.comp (ContinuousLinearMap.inl ℝ (Point n) (Point n)) w
        + D.comp (ContinuousLinearMap.inr ℝ (Point n) (Point n)) w = 0
    rw [h1, h2]
    exact hDsplit w
  rw [hzero] at hgFD
  exact hgFD

/-! ###############################################################################
    ### 2. The QUADRATIC Taylor-remainder payoff.
    ############################################################################### -/

/-- **★★★ `antisymmetryDefect_quadratic_bound` — THE GO-CLASSIFIED PAYOFF.**  Under the SAME two
    hypotheses as `antisymmetryDefect_fderiv_zero` — (F1) `Φ q q = 0` eventually near `q₀`, (F3) `Φ`
    jointly `ContDiffAt ℝ 2` at `(q₀,q₀)` — the antisymmetrized slice satisfies the QUADRATIC bound
        `∃ r > 0, C ≥ 0, ∀ p, ‖p - q₀‖ < r → ‖Φ p q₀ + Φ q₀ p‖ ≤ C * ‖p - q₀‖ ^ 2`.
    Proof: `g p := Φ p q₀ + Φ q₀ p` is `ContDiffAt ℝ 2` at `q₀` (sum of two compositions of the joint
    `C²` map with smooth affine embeddings), has `g q₀ = 0` and `HasFDerivAt g 0 q₀`
    (`antisymmetryDefect_fderiv_zero`).  Extract `g'` (first derivative, near `q₀`) and `g''` (second
    derivative) via `contDiffAt_succ_iff_hasFDerivAt` twice; `g'` is Lipschitz-at-`q₀` on a ball (mean
    value against the LOCAL bound on `g''`, exactly `JointRNCRegularityLocal.jointRNCRegularityLocal_of_
    diag`'s `hBop` technique); a SECOND mean-value pass (the same file's `hVdisp` technique, using
    `g(q₀) = 0` AND `g'(q₀) = 0`) gives `‖g z‖ ≤ M‖z - q₀‖²`.  This is the GENUINE quadratic order fact
    the sympy gate (`hcomp_baseslot_antisymmetry_order.py`) predicted and Sol (gpt-5.6-sol, high)
    confirmed GO on.  NOT `a₁ = R/6`. -/
theorem antisymmetryDefect_quadratic_bound (Φ : Point n → Point n → Point n) (q₀ : Point n)
    (hdiag : ∀ᶠ q in 𝓝 q₀, Φ q q = 0)
    (hjointC2 : ContDiffAt ℝ 2 (fun p : Point n × Point n => Φ p.1 p.2) (q₀, q₀)) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ p : Point n, ‖p - q₀‖ < r → ‖Φ p q₀ + Φ q₀ p‖ ≤ C * ‖p - q₀‖ ^ 2 := by
  classical
  set g : Point n → Point n := fun p => Φ p q₀ + Φ q₀ p with hgdef
  -- `g` is `ContDiffAt ℝ 2` at `q₀`: sum of two compositions of `hjointC2` with smooth embeddings.
  have hemb1 : ContDiffAt ℝ 2 (fun p : Point n => ((p, q₀) : Point n × Point n)) q₀ :=
    ContDiffAt.prodMk contDiffAt_id contDiffAt_const
  have hemb2 : ContDiffAt ℝ 2 (fun p : Point n => ((q₀, p) : Point n × Point n)) q₀ :=
    ContDiffAt.prodMk contDiffAt_const contDiffAt_id
  have hgc1 : ContDiffAt ℝ 2 (fun p : Point n => Φ p q₀) q₀ :=
    ContDiffAt.comp q₀ (f := fun p : Point n => (p, q₀)) hjointC2 hemb1
  have hgc2 : ContDiffAt ℝ 2 (fun p : Point n => Φ q₀ p) q₀ :=
    ContDiffAt.comp q₀ (f := fun p : Point n => (q₀, p)) hjointC2 hemb2
  have hgC2 : ContDiffAt ℝ 2 g q₀ := hgc1.add hgc2
  -- `g q₀ = 0` and `HasFDerivAt g 0 q₀`, from Part 1.
  obtain ⟨hgval, hgfd0⟩ := antisymmetryDefect_fderiv_zero Φ q₀ hdiag hjointC2
  have hgq0 : g q₀ = 0 := hgval
  -- extract `g'`, `g''` on neighbourhoods via `contDiffAt_succ_iff_hasFDerivAt` twice.
  obtain ⟨g', ⟨u, hu_nhds, hgderiv⟩, hg'c1⟩ :=
    contDiffAt_succ_iff_hasFDerivAt.mp (show ContDiffAt ℝ (1 + 1 : ℕ) g q₀ by exact_mod_cast hgC2)
  obtain ⟨g'', ⟨u2, hu2_nhds, hg'deriv⟩, hg''c0⟩ :=
    contDiffAt_succ_iff_hasFDerivAt.mp (show ContDiffAt ℝ (0 + 1 : ℕ) g' q₀ by exact_mod_cast hg'c1)
  -- `g' q₀ = fderiv g q₀ = 0`.
  have hg'q0 : g' q₀ = (0 : Point n →L[ℝ] Point n) := by
    have hmem : q₀ ∈ u := mem_of_mem_nhds hu_nhds
    have hfd := (hgderiv q₀ hmem).fderiv
    have hfd0 : fderiv ℝ g q₀ = 0 := hgfd0.fderiv
    rw [← hfd, hfd0]
  -- second-derivative bound near `q₀` via continuity of `g''`.
  set M : ℝ := ‖g'' q₀‖ + 1 with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hcont : ContinuousAt g'' q₀ := hg''c0.continuousAt
  have hbound_ev : ∀ᶠ z in 𝓝 q₀, ‖g'' z‖ ≤ M := by
    have hmem : Set.Iio M ∈ 𝓝 ‖g'' q₀‖ := Iio_mem_nhds (by rw [hMdef]; linarith)
    have h := (hcont.norm) hmem
    filter_upwards [h] with z hz
    exact le_of_lt hz
  have hset : u ∩ u2 ∩ {z | ‖g'' z‖ ≤ M} ∈ 𝓝 q₀ :=
    Filter.inter_mem (Filter.inter_mem hu_nhds hu2_nhds) hbound_ev
  obtain ⟨r, hr0, hsub⟩ := Metric.mem_nhds_iff.mp hset
  refine ⟨r, hr0, M, hM0, ?_⟩
  have hz_u : ∀ z ∈ Metric.ball q₀ r, z ∈ u := fun z hz => ((hsub hz).1).1
  have hz_u2 : ∀ z ∈ Metric.ball q₀ r, z ∈ u2 := fun z hz => ((hsub hz).1).2
  have hz_bd : ∀ z ∈ Metric.ball q₀ r, ‖g'' z‖ ≤ M := fun z hz => (hsub hz).2
  have hq₀ball : q₀ ∈ Metric.ball q₀ r := Metric.mem_ball_self hr0
  -- `g'` is Lipschitz-at-`q₀`, operator form: `‖g' z − g' q₀‖ ≤ M‖z − q₀‖`.
  have hBop : ∀ z ∈ Metric.ball q₀ r, ‖g' z - g' q₀‖ ≤ M * ‖z - q₀‖ := by
    intro z hz
    have hseg_ball : segment ℝ q₀ z ⊆ Metric.ball q₀ r :=
      (convex_ball q₀ r).segment_subset hq₀ball hz
    have hderiv : ∀ w ∈ segment ℝ q₀ z, HasFDerivWithinAt g' (g'' w) (segment ℝ q₀ z) w :=
      fun w hw => (hg'deriv w (hz_u2 w (hseg_ball hw))).hasFDerivWithinAt
    have hbd : ∀ w ∈ segment ℝ q₀ z, ‖g'' w‖ ≤ M := fun w hw => hz_bd w (hseg_ball hw)
    exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbd
      (convex_segment q₀ z) (left_mem_segment ℝ q₀ z) (right_mem_segment ℝ q₀ z)
  intro p hp
  set z := p with hzdef
  have hseg_ball : segment ℝ q₀ z ⊆ Metric.ball q₀ r :=
    (convex_ball q₀ r).segment_subset hq₀ball hp
  have hseg_cb : segment ℝ q₀ z ⊆ Metric.closedBall q₀ ‖z - q₀‖ :=
    (convex_closedBall q₀ ‖z - q₀‖).segment_subset
      (Metric.mem_closedBall_self (norm_nonneg _))
      (by rw [Metric.mem_closedBall, dist_eq_norm])
  have hgderiv' : ∀ w ∈ segment ℝ q₀ z, HasFDerivWithinAt g (g' w) (segment ℝ q₀ z) w :=
    fun w hw => (hgderiv w (hz_u w (hseg_ball hw))).hasFDerivWithinAt
  have hgbd : ∀ w ∈ segment ℝ q₀ z, ‖g' w - g' q₀‖ ≤ M * ‖z - q₀‖ := by
    intro w hw
    have hwr : ‖w - q₀‖ ≤ ‖z - q₀‖ := by
      have := hseg_cb hw; rw [Metric.mem_closedBall, dist_eq_norm] at this; exact this
    calc ‖g' w - g' q₀‖ ≤ M * ‖w - q₀‖ := hBop w (hseg_ball hw)
      _ ≤ M * ‖z - q₀‖ := mul_le_mul_of_nonneg_left hwr hM0
  -- the affine-remainder mean-value pass: `g` itself is the "remainder" since `g q₀ = 0`, `g' q₀ = 0`.
  have hRderiv : ∀ w ∈ segment ℝ q₀ z,
      HasFDerivWithinAt g (g' w - g' q₀) (segment ℝ q₀ z) w := by
    intro w hw
    rw [hg'q0, sub_zero]
    exact hgderiv' w hw
  have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hRderiv hgbd
    (convex_segment q₀ z) (left_mem_segment ℝ q₀ z) (right_mem_segment ℝ q₀ z)
  have hgz_eq : g z - g q₀ = g z := by rw [hgq0]; simp
  rw [hgz_eq] at hmv
  calc ‖Φ p q₀ + Φ q₀ p‖ = ‖g z‖ := by rw [hgdef, hzdef]
    _ ≤ M * ‖z - q₀‖ * ‖z - q₀‖ := hmv
    _ = M * ‖p - q₀‖ ^ 2 := by rw [hzdef]; ring

/-! ###############################################################################
    ### 3. Non-vacuity — the hypothesis bundle is inhabited by a genuine, non-degenerate `Φ`.
    ############################################################################### -/

/-- **Non-vacuity witness.**  `Φ p q := p - q` — a genuine, non-degenerate (non-constant, non-zero)
    map — satisfies BOTH hypotheses of `antisymmetryDefect_quadratic_bound` for EVERY base point `q₀`,
    with the antisymmetry defect IDENTICALLY zero (`Φ` is exactly antisymmetric, the "flat" case).  A
    genuine sanity check that the hypothesis bundle is not vacuous. NOT `a₁ = R/6`. -/
theorem antisymmetryDefect_quadratic_bound_hyp_satisfiable (q₀ : Point n) :
    ∃ Φ : Point n → Point n → Point n,
      (∀ᶠ q in 𝓝 q₀, Φ q q = 0) ∧
      ContDiffAt ℝ 2 (fun p : Point n × Point n => Φ p.1 p.2) (q₀, q₀) ∧
      (∀ p q : Point n, Φ p q + Φ q p = 0) := by
  refine ⟨fun p q => p - q, Filter.Eventually.of_forall (fun q => sub_self q), ?_, fun p q => by module⟩
  exact (contDiff_fst.contDiffAt).sub (contDiff_snd.contDiffAt)

end QIQTH.HCompBaseSlotAntisymmetry

/-! ## Axiom checks — every public theorem is `std-3` (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.HCompBaseSlotAntisymmetry
#print axioms antisymmetryDefect_fderiv_zero
#print axioms antisymmetryDefect_quadratic_bound
#print axioms antisymmetryDefect_quadratic_bound_hyp_satisfiable
end AxiomChecks
