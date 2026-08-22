/-
  BaseSlotDerivFromAntisymEvalSlot — J4-1004 (Sol-consulted GO, `gpt-5.6-sol` high, 2026-08-22): the
  ABSTRACT "base-slot derivative from antisymmetry + eval-slot normalization" brick, resolving the
  precise gap cp884 diagnosed: generalizing `ChartW0Fderiv`/`BaseVaryingIFTPackage`'s base-direction
  derivative fact `D₁Φ(q₀,q₀) = -Id` from `q₀ = 0` to a GENERAL base point `q₀`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  pure real-analysis brick, fully abstract in the map `Φ` (mirrors `HCompBaseSlotAntisymmetryQuadratic`'s
  abstraction discipline).  It does NOT instantiate `uniformInverseChart`, does NOT touch `kPrime`,
  `heatHessMult`, `hcomp`, `herr_gate`/`hmin_gate` literally.  No `sorry`, no new axioms, no `:= True`,
  no vacuous / unsatisfiable hypothesis, none equal to the conclusion, no existing file edited.
  `hCConv`/`hcomp` NOT closed.  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`,
  UNCHANGED.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE PRECISE GAP (cp884, re-verified against `HCompBaseSlotAntisymmetryQuadratic.lean` and
  `JointRNCRegularityInterfaceLocal.lean` rather than trusted from the dispatch prose).

  `ChartW0Fderiv.chartW0_hasFDerivAt_zero` / `BaseVaryingIFTPackage.baseVaryingChart_hasFDerivAt_center`
  prove the BASE-direction derivative `D₁Φ(0,0) = -Id` for `Φ(p,v) := uniformInverseChart g gi hC hK p v`
  — but ONLY at `q₀ = 0`, via the banked quadratic displacement bound `chartW0_displacement`, which is
  itself proved by an `ApproximatesLinearOn`/bootstrap argument specific to the origin base point.  There
  is no direct route generalizing that specific argument to a general `q₀`.

  `HCompBaseSlotAntisymmetryQuadratic.antisymmetryDefect_fderiv_zero` proves, for a GENERAL `q₀`, that
  the SUM `D₁Φ(q₀,q₀) + D₂Φ(q₀,q₀) = 0` (as `HasFDerivAt (fun p => Φ p q₀ + Φ q₀ p) 0 q₀`), from ONLY
  the diagonal-vanishing (F1) and joint `ContDiffAt ℝ 2` (F3) — it says NOTHING about either partial
  derivative individually.

  `JointRNCRegularityInterfaceLocal.uniformInverseChart_slice_fderiv_id_diag` ALREADY proves, for a
  GENERAL `q₀`, the EVAL-slot (D₂) derivative is the identity: `fderiv (fun v => Φ q₀ v) q₀ = Id`.

  So the "genuinely missing ingredient" the cp884 dispatch flagged (an eval-slot linearization at general
  `q₀`) turns out to ALREADY BE BANKED under a different name (J4-856/857's diagonal slice-fderiv fact) —
  the dispatch's own diagnosis was STALE (it checked only `ChartW0Fderiv`/`BaseVaryingIFTPackage`, not
  `JointRNCRegularityInterfaceLocal`).  What is genuinely NEW and was NOT yet derivable from any single
  banked theorem is the BASE-slot (D₁) individual derivative at general `q₀`: combining the antisymmetry
  SUM fact with the already-banked eval-slot (D₂) fact via elementary subtraction extracts D₁ INDIVIDUALLY.
  Sol (`gpt-5.6-sol`, high) confirmed this combination is sound and non-trivial-but-genuinely-new (GO,
  2026-08-22): "the packaged general-q₀ base-slot derivative and displacement theorem appears genuinely
  missing and is exactly useful downstream."

  ## WHAT LANDS (ns `QIQTH.BaseSlotDerivFromAntisymEvalSlot`), fully abstract in `Φ`.
    • ★★ `baseSlot_fderiv_neg_id_of_antisym_evalSlot` — Step A: given (F1) diagonal vanishing, (F3) joint
      `ContDiffAt ℝ 2`, and (F4) the eval-slot normalization `HasFDerivAt (fun v => Φ q₀ v) Id q₀`,
      derive `HasFDerivAt (fun p => Φ p q₀) (-Id) q₀` — by subtracting (F4)'s derivative from the
      antisymmetrized-sum's (zero) derivative via `HasFDerivAt.sub` and the pointwise identity
      `(Φ p q₀ + Φ q₀ p) - Φ q₀ p = Φ p q₀`.
    • ★★★ `baseSlot_quadratic_displacement_of_antisym_evalSlot` — Step B: THE PAYOFF, under the SAME
      (F1)/(F3)/(F4): the base-slot displacement is QUADRATIC at general `q₀`:
          `∃ r > 0, C ≥ 0, ∀ p, ‖p - q₀‖ < r → ‖Φ p q₀ + (p - q₀)‖ ≤ C * ‖p - q₀‖²`.
      Proof: the SAME mean-value-twice technique already used TWICE in this codebase
      (`JointRNCRegularityLocal.jointRNCRegularityLocal_of_diag`'s `hVdisp`, and
      `HCompBaseSlotAntisymmetryQuadratic.antisymmetryDefect_quadratic_bound`), applied to
      `h p := Φ p q₀` directly, using `h q₀ = 0` (F1), `h' q₀ = -Id` (Step A), `h` `ContDiffAt ℝ 2` at
      `q₀` (F3 composed with `p ↦ (p, q₀)`).
    • `baseSlot_hyp_satisfiable` — non-vacuity: `Φ p q := p - q` (exactly antisymmetric) satisfies all of
      (F1)/(F3)/(F4) for every `q₀`, with the payoff's defect identically zero.

  ## THE SYMPY GATE.  `docs/qg_roadmap/rnc_sympy/baseslot_deriv_from_antisym_and_evalslot.py` verifies
  symbolically (a) the linear-algebra step `D₁Φ(q₀,q₀) = 0 - Id = -Id` with a GENERIC 2×2 matrix standing
  in for `D₂Φ(q₀,q₀)` (not hard-coded to `Id`) before specializing, confirming the derivation is a pure
  linear identity, not an artefact of the specific value `Id`; (b) the quadratic Taylor-remainder rate
  via an extremal 1-D model `h(x) = -(x-q₀) + (M/2)(x-q₀)²` with `h(q₀)=0`, `h'(q₀)=-1`, `h''≡M`,
  confirming the remainder `h(p)+(p-q₀)` is exactly `O((p-q₀)²)` (strictly higher order than the linear
  term, `o(|p-q₀|)`).  Sol (`gpt-5.6-sol`, high, 2026-08-22) independently confirmed the derivation
  GO, no hidden gap in the `HasFDerivAt.sub` step or the re-use of `antisymmetryDefect_fderiv_zero`.

  ## HONEST DISTANCE.  Fully abstract in `Φ`: does NOT instantiate `uniformInverseChart`. See the
  companion concrete file `UniformInverseChartBaseSlotDisplacementGeneralQ0.lean` for the instantiation.
  Neither file touches `kPrime`/`heatHessMult`/`hcomp` literally, does the base-slot change of variables,
  or generalizes `herr_gate`/`hmin_gate` (which additionally need `rncRadialSq`-comparison and gate
  machinery re-derived at general `q₀`, a further, separate engineering step).  `hCConv` NOT closed.
  `a₁ = R/6` remains STRICTLY CONDITIONAL on `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.HCompBaseSlotAntisymmetryQuadratic

open Filter
open QIQTH.Curvature QIQTH.ExpMap
open scoped Topology

namespace QIQTH.BaseSlotDerivFromAntisymEvalSlot

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### Step A — the base-slot derivative, extracted individually via subtraction.
    ############################################################################### -/

/-- **★★ `baseSlot_fderiv_neg_id_of_antisym_evalSlot` — Step A.**  For `Φ : Point n → Point n → Point n`,
    a base point `q₀`, (F1) `Φ q q = 0` eventually near `q₀`, (F3) `Φ` jointly `ContDiffAt ℝ 2` at
    `(q₀,q₀)`, and (F4) the EVAL-slot normalization `HasFDerivAt (fun v => Φ q₀ v) Id q₀`: the BASE-slot
    derivative is `-Id`:  `HasFDerivAt (fun p => Φ p q₀) (-Id) q₀`.  Proof: `g p := Φ p q₀ + Φ q₀ p` has
    `HasFDerivAt g 0 q₀` (`antisymmetryDefect_fderiv_zero`, F1+F3 only); subtract (F4)'s derivative via
    `HasFDerivAt.sub`, using the pointwise identity `(Φ p q₀ + Φ q₀ p) - Φ q₀ p = Φ p q₀`.  NOT
    `a₁ = R/6`. -/
theorem baseSlot_fderiv_neg_id_of_antisym_evalSlot (Φ : Point n → Point n → Point n) (q₀ : Point n)
    (hdiag : ∀ᶠ q in 𝓝 q₀, Φ q q = 0)
    (hjointC2 : ContDiffAt ℝ 2 (fun p : Point n × Point n => Φ p.1 p.2) (q₀, q₀))
    (hevalId : HasFDerivAt (fun v => Φ q₀ v) (ContinuousLinearMap.id ℝ (Point n)) q₀) :
    HasFDerivAt (fun p => Φ p q₀) (-(ContinuousLinearMap.id ℝ (Point n))) q₀ := by
  obtain ⟨_, hgfd0⟩ :=
    QIQTH.HCompBaseSlotAntisymmetry.antisymmetryDefect_fderiv_zero Φ q₀ hdiag hjointC2
  have hs := hgfd0.sub hevalId
  have heq : (fun p => Φ p q₀) =ᶠ[𝓝 q₀]
      ((fun p => Φ p q₀ + Φ q₀ p) - fun v => Φ q₀ v) :=
    Filter.Eventually.of_forall (fun p => by simp)
  simpa using hs.congr_of_eventuallyEq heq

/-! ###############################################################################
    ### Step B — the base-slot displacement, QUADRATIC at general `q₀`.
    ############################################################################### -/

/-- **★★★ `baseSlot_quadratic_displacement_of_antisym_evalSlot` — Step B, THE PAYOFF.**  Under the SAME
    (F1)/(F3)/(F4) as Step A, the base-slot displacement of `Φ` is QUADRATIC at general `q₀`:
        `∃ r > 0, C ≥ 0, ∀ p, ‖p - q₀‖ < r → ‖Φ p q₀ + (p - q₀)‖ ≤ C * ‖p - q₀‖²`.
    Genuinely generalizes `ChartW0Fderiv`/`BaseVaryingIFTPackage.chartW0_displacement`'s
    `q₀ = 0`-only quadratic base-displacement bound to a GENERAL base point, via the mean-value-twice
    technique already used twice in this codebase.  NOT `a₁ = R/6`. -/
theorem baseSlot_quadratic_displacement_of_antisym_evalSlot (Φ : Point n → Point n → Point n)
    (q₀ : Point n)
    (hdiag : ∀ᶠ q in 𝓝 q₀, Φ q q = 0)
    (hjointC2 : ContDiffAt ℝ 2 (fun p : Point n × Point n => Φ p.1 p.2) (q₀, q₀))
    (hevalId : HasFDerivAt (fun v => Φ q₀ v) (ContinuousLinearMap.id ℝ (Point n)) q₀) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ p : Point n, ‖p - q₀‖ < r → ‖Φ p q₀ + (p - q₀)‖ ≤ C * ‖p - q₀‖ ^ 2 := by
  classical
  set h : Point n → Point n := fun p => Φ p q₀ with hhdef
  have hval0 : Φ q₀ q₀ = 0 := hdiag.self_of_nhds
  have hh0 : h q₀ = 0 := by rw [hhdef]; exact hval0
  have hh' : HasFDerivAt h (-(ContinuousLinearMap.id ℝ (Point n))) q₀ :=
    baseSlot_fderiv_neg_id_of_antisym_evalSlot Φ q₀ hdiag hjointC2 hevalId
  have hemb1 : ContDiffAt ℝ 2 (fun p : Point n => ((p, q₀) : Point n × Point n)) q₀ :=
    ContDiffAt.prodMk contDiffAt_id contDiffAt_const
  have hhC2 : ContDiffAt ℝ 2 h q₀ :=
    ContDiffAt.comp q₀ (f := fun p : Point n => (p, q₀)) hjointC2 hemb1
  -- extract `h'`, `h''` on neighbourhoods via `contDiffAt_succ_iff_hasFDerivAt` twice.
  obtain ⟨h', ⟨u, hu_nhds, hderiv⟩, hh'c1⟩ :=
    contDiffAt_succ_iff_hasFDerivAt.mp (show ContDiffAt ℝ (1 + 1 : ℕ) h q₀ by exact_mod_cast hhC2)
  obtain ⟨h'', ⟨u2, hu2_nhds, hh'deriv⟩, hh''c0⟩ :=
    contDiffAt_succ_iff_hasFDerivAt.mp (show ContDiffAt ℝ (0 + 1 : ℕ) h' q₀ by exact_mod_cast hh'c1)
  -- `h' q₀ = fderiv h q₀ = -Id`.
  have hh'q0 : h' q₀ = -(ContinuousLinearMap.id ℝ (Point n)) := by
    have hmem : q₀ ∈ u := mem_of_mem_nhds hu_nhds
    have hfd := (hderiv q₀ hmem).fderiv
    have hfd0 : fderiv ℝ h q₀ = -(ContinuousLinearMap.id ℝ (Point n)) := hh'.fderiv
    rw [← hfd, hfd0]
  -- second-derivative bound near `q₀` via continuity of `h''`.
  set M : ℝ := ‖h'' q₀‖ + 1 with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hcont : ContinuousAt h'' q₀ := hh''c0.continuousAt
  have hbound_ev : ∀ᶠ z in 𝓝 q₀, ‖h'' z‖ ≤ M := by
    have hmem : Set.Iio M ∈ 𝓝 ‖h'' q₀‖ := Iio_mem_nhds (by rw [hMdef]; linarith)
    have h := (hcont.norm) hmem
    filter_upwards [h] with z hz
    exact le_of_lt hz
  have hset : u ∩ u2 ∩ {z | ‖h'' z‖ ≤ M} ∈ 𝓝 q₀ :=
    Filter.inter_mem (Filter.inter_mem hu_nhds hu2_nhds) hbound_ev
  obtain ⟨r, hr0, hsub⟩ := Metric.mem_nhds_iff.mp hset
  refine ⟨r, hr0, M, hM0, ?_⟩
  have hz_u : ∀ z ∈ Metric.ball q₀ r, z ∈ u := fun z hz => ((hsub hz).1).1
  have hz_u2 : ∀ z ∈ Metric.ball q₀ r, z ∈ u2 := fun z hz => ((hsub hz).1).2
  have hz_bd : ∀ z ∈ Metric.ball q₀ r, ‖h'' z‖ ≤ M := fun z hz => (hsub hz).2
  have hq₀ball : q₀ ∈ Metric.ball q₀ r := Metric.mem_ball_self hr0
  -- `h'` is Lipschitz-at-`q₀`, operator form: `‖h' z − h' q₀‖ ≤ M‖z − q₀‖`.
  have hBop : ∀ z ∈ Metric.ball q₀ r, ‖h' z - h' q₀‖ ≤ M * ‖z - q₀‖ := by
    intro z hz
    have hseg_ball : segment ℝ q₀ z ⊆ Metric.ball q₀ r :=
      (convex_ball q₀ r).segment_subset hq₀ball hz
    have hd : ∀ w ∈ segment ℝ q₀ z, HasFDerivWithinAt h' (h'' w) (segment ℝ q₀ z) w :=
      fun w hw => (hh'deriv w (hz_u2 w (hseg_ball hw))).hasFDerivWithinAt
    have hbd : ∀ w ∈ segment ℝ q₀ z, ‖h'' w‖ ≤ M := fun w hw => hz_bd w (hseg_ball hw)
    exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hd hbd
      (convex_segment q₀ z) (left_mem_segment ℝ q₀ z) (right_mem_segment ℝ q₀ z)
  intro p hp
  set z := p with hzdef
  have hseg_ball : segment ℝ q₀ z ⊆ Metric.ball q₀ r :=
    (convex_ball q₀ r).segment_subset hq₀ball hp
  have hseg_cb : segment ℝ q₀ z ⊆ Metric.closedBall q₀ ‖z - q₀‖ :=
    (convex_closedBall q₀ ‖z - q₀‖).segment_subset
      (Metric.mem_closedBall_self (norm_nonneg _))
      (by rw [Metric.mem_closedBall, dist_eq_norm])
  -- the "affine-remainder" pass: `R w := h w + (w - q₀)` has `R q₀ = 0`, `R' q₀ = 0`.
  set R : Point n → Point n := fun w => h w + (w - q₀) with hRdef
  have hRderiv : ∀ w ∈ segment ℝ q₀ z,
      HasFDerivWithinAt R (h' w + ContinuousLinearMap.id ℝ (Point n)) (segment ℝ q₀ z) w := by
    intro w hw
    have hhw : HasFDerivAt h (h' w) w := hderiv w (hz_u w (hseg_ball hw))
    have haff : HasFDerivAt (fun w : Point n => w - q₀) (ContinuousLinearMap.id ℝ (Point n)) w :=
      (hasFDerivAt_id w).sub_const q₀
    exact (hhw.add haff).hasFDerivWithinAt
  have hRbd : ∀ w ∈ segment ℝ q₀ z,
      ‖h' w + ContinuousLinearMap.id ℝ (Point n)‖ ≤ M * ‖z - q₀‖ := by
    intro w hw
    have hwr : ‖w - q₀‖ ≤ ‖z - q₀‖ := by
      have := hseg_cb hw; rw [Metric.mem_closedBall, dist_eq_norm] at this; exact this
    have heq : h' w + ContinuousLinearMap.id ℝ (Point n) = h' w - h' q₀ := by
      rw [hh'q0]; abel
    rw [heq]
    calc ‖h' w - h' q₀‖ ≤ M * ‖w - q₀‖ := hBop w (hseg_ball hw)
      _ ≤ M * ‖z - q₀‖ := mul_le_mul_of_nonneg_left hwr hM0
  have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hRderiv hRbd
    (convex_segment q₀ z) (left_mem_segment ℝ q₀ z) (right_mem_segment ℝ q₀ z)
  have hRq₀ : R q₀ = 0 := by rw [hRdef]; simp [hh0]
  rw [hRq₀] at hmv
  calc ‖Φ p q₀ + (p - q₀)‖ = ‖R z - 0‖ := by rw [hRdef, hhdef, hzdef]; simp
    _ ≤ M * ‖z - q₀‖ * ‖z - q₀‖ := hmv
    _ = M * ‖p - q₀‖ ^ 2 := by rw [hzdef]; ring

/-! ###############################################################################
    ### Non-vacuity — the (F1)/(F3)/(F4) bundle is inhabited by a genuine, non-degenerate `Φ`.
    ############################################################################### -/

/-- **Non-vacuity witness.**  `Φ p q := q - p` satisfies (F1)/(F3)/(F4) for EVERY `q₀`, with the
    base-slot displacement defect IDENTICALLY zero (the "flat" case, `Φ` exactly antisymmetric).
    NOT `a₁ = R/6`. -/
theorem baseSlot_hyp_satisfiable (q₀ : Point n) :
    ∃ Φ : Point n → Point n → Point n,
      (∀ᶠ q in 𝓝 q₀, Φ q q = 0) ∧
      ContDiffAt ℝ 2 (fun p : Point n × Point n => Φ p.1 p.2) (q₀, q₀) ∧
      HasFDerivAt (fun v => Φ q₀ v) (ContinuousLinearMap.id ℝ (Point n)) q₀ ∧
      (∀ p : Point n, Φ p q₀ + (p - q₀) = 0) := by
  refine ⟨fun p q => q - p, Filter.Eventually.of_forall (fun q => sub_self q),
    (contDiff_snd.contDiffAt).sub (contDiff_fst.contDiffAt),
    (hasFDerivAt_id q₀).sub_const q₀, fun p => by module⟩

end QIQTH.BaseSlotDerivFromAntisymEvalSlot

/-! ## Axiom checks — std-3 (propext, Classical.choice, Quot.sound). -/
section AxiomChecks
open QIQTH.BaseSlotDerivFromAntisymEvalSlot
#print axioms baseSlot_fderiv_neg_id_of_antisym_evalSlot
#print axioms baseSlot_quadratic_displacement_of_antisym_evalSlot
#print axioms baseSlot_hyp_satisfiable
end AxiomChecks
