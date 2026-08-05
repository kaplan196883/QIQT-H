/-
  WideBoundaryLimDischarge — J4-267: the W1 / `hBoundaryLim` wall, addressed through the wide bank.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  wide-route boundary brick.  No `sorry` (header prose excepted), no new axioms, no `:= True`, no
  vacuous / unsatisfiable hypotheses, no hypothesis equal to (or trivially yielding) the conclusion, no
  existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (A) THE W1 WALL, STATED PRECISELY AT THE CONCRETE GATE.

  The `hBoundaryLim` slot consumed by `TruncatedDuhamelData.truncatedDuhamelCore_of_daLim` (and hence by
  `EnvelopeCoreDischarge.core_of_v2prime_data`) is the pointwise-at-`t` boundary limit
      `hBoundaryLim : Tendsto (fun m => BoundaryTrunc Wit F m t) atTop (𝓝 (F t 0 0))`,
      with  `F := leviSeries (heatOp g gi Wit)`,   `Wit := vanVleckGatedWitness g gi hChr hK S a b`,
  where (`TruncatedDuhamel.BoundaryTrunc`, def, `u−(u−ε_m)=ε_m`)
      `BoundaryTrunc Wit F m t = ∫ z, Wit (ε_m) 0 z · F (t−ε_m) z 0`.

  The ONLY provider of `hBoundaryLim` in the repo is `HeatResidualBound.boundaryTrunc_tendsto`
  (`DuhamelLimitWiring`), a pointwise specialisation of `BoundaryAssembly.boundary_tendstoLocallyUniformlyOn`.
  That engine's load-bearing hypothesis is the EXACT-WIDTH near-diagonal factorisation
      `hAnear : ∀ τ ∈ Ioo 0 τ₀, ∀ z ∈ ball 0 r₀,   Wit τ 0 z = gaussDdim τ z · (u₀ z + τ · u₁ z)`,
  used at exactly ONE place — `BoundaryAssembly.boundary_tendstoLocallyUniformlyOn`, inside the sub-block
  `hball_eq` (line 399: `rw [hAnear (epsSeq m) hεIoo z hz]; ring`) — where the base-point width-`τ`
  Gaussian `gaussDdim τ z` is factored out so the MAIN term becomes the base-point approximate identity
  `∫ z, gaussDdim (ε_m) z · (u₀ z · B …)` handled by `tendstoUniformlyOn_integral_gaussDdim_smul_family`
  (T2u).

  ★ W1 (the wall).  For the concrete gated van-Vleck witness this exact-width `hAnear` is **FALSE**:
  `witness_zero_eq_gauss_mul_amp` gives the honest factorisation
      `Wit τ 0 z = gaussDdim τ (W₀ z) · chartFieldAmp … τ z 0`,   `W₀ z = uniformInverseChart … z 0`,
  a Gaussian peaked at the CHART IMAGE `W₀ z`, NOT at the base point `z`.  The exact-width ratio
  `gaussDdim τ (W₀ z) / gaussDdim τ z = exp((‖z‖²−‖W₀ z‖²)/(4τ)) → ∞` as `τ → 0` whenever `‖W₀ z‖ < ‖z‖`
  (Sol consult #4; `DataPileWitnessAudit` W1).  So `hAnear` cannot be supplied at the concrete gate, and
  carrying it would be an UNSATISFIABLE hypothesis the firewall forbids.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (B) WHAT THE WIDE BANK CAN AND CANNOT DO FOR `hBoundaryLim` — AND THE CONSUMER-RETHREAD MAP.

  The wide bank replaces the exact-width DOMINATION forms:
    * `WideWitnessAmplitude.WideAmplitudeData.zeroth_domination(_global)` — the ZEROTH wide domination
        `|Wit τ 0 z| ≤ C · gaussDdim (lam·τ) z`   (`0 < τ ≤ τ₀`; global via the carried support fact),
      SATISFIABLE at the concrete gate (it is a genuine wide-bank output for the van-Vleck witness);
    * `WideSliverBoundary.gaussDdim_wide_approx_identity` (B1) — the wide approximate identity
        `∫ z, gaussDdim (lam·τ) z · f z → f 0`   in `𝓝[>] 0`.

  ★ HONEST LIMITATION.  Neither discharges the LIMIT-VALUE member `hBoundaryLim` at the concrete gate:
  the wide approximate identity B1 samples a BASE-POINT Gaussian `gaussDdim (lam·τ) z`, whereas the
  concrete boundary integrand carries the CHART-IMAGE Gaussian `gaussDdim (ε_m) (W₀ z)`.  The mass-one
  sampling that pins the boundary limit to the EXACT value `F t 0 0` (rather than a mere bound) requires
  a CHANGE-OF-VARIABLES approximate identity with the van-Vleck normalisation — see the minimal missing
  lemma (C) below.  This is genuinely-new analysis, absent from the wide bank (whose transfer machinery
  is a Gaussian-domination BOUND, not a mass-preserving push-forward).

  CONSUMER-RETHREAD MAP (precise).
    • Consumer         : `BoundaryAssembly.boundary_tendstoLocallyUniformlyOn`.
    • Binder to drop   : `hAnear` (exact-width factorisation) — FALSE at the concrete gate (W1).
    • Sole use site    : sub-block `hball_eq` (`rw [hAnear …]; ring`), which rewrites the ball integral
                         into the base-point Gaussian × `u₀`/`u₁` split feeding the T2u MAIN convergence.
    • Wide replacement : `gaussDdim_wide_approx_identity` (B1) would supply the MAIN limit IF the boundary
                         integrand were a base-point Gaussian; it is NOT (chart-image peak), so the
                         rethread is BLOCKED on the change-of-variables lemma (C).  The DOMINATION side of
                         the rethread (tightness / integrability envelope of the boundary sequence) IS
                         discharged by the wide zeroth domination — banked here as
                         `wide_boundaryTrunc_bound` / `wide_boundaryTrunc_bound_concrete`.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## WHAT LANDS HERE (genuine, green, wide-bank-driven — the boundary DOMINATION member).

    (S0) `wide_boundary_inner_bound` — the ZEROTH-order per-evaluation wide bound (the boundary analogue
         of `WideSliverBoundary.wide_second_inner_slice_bound`, with the `τ⁻¹` removed): from the wide
         zeroth domination `|H τ z| ≤ C·gaussDdim (lam·τ) z` (`0 < τ ≤ τ₀`) and `|F| ≤ C_L·gaussDdim (2s)`,
             `‖∫ z, H (u−s) z · F s z 0‖ ≤ C·C_L·gaussDdim (lam(u−s)+2s) 0`,
         via the same-point Chapman–Kolmogorov mass `gaussDdim_selfmul_integral`.
    (S1) `wide_boundaryTrunc_bound` — the `BoundaryTrunc` boundedness member (abstract kernel): the
         boundary sequence is envelope-dominated,
             `|BoundaryTrunc Wit F m t| ≤ C·C_L·gaussDdim (lam·ε_m + 2(t−ε_m)) 0`,
         which stays BOUNDED as `m → ∞` (width `→ 2t > 0`).  A genuine tightness fact — NOT the limit
         value (that is the W1-blocked member above), NOT vacuous.
    (S2) `wide_boundaryTrunc_bound_concrete` — (S1) at the CONCRETE van-Vleck gate: from a
         `WideWitnessAmplitude.WideAmplitudeData` + its support fact, the wide zeroth domination
         (`zeroth_domination_global`) feeds (S1), giving the boundary envelope bound for
         `Wit := vanVleckGatedWitness g gi hC hK S P.D.a P.D.b`.  This is ONE boundary-pile (boundedness)
         member discharged at the concrete gate via the wide bank.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## (C) THE MINIMAL MISSING LEMMA (for external consult) — the chart-image approximate identity.

  To discharge the LIMIT-VALUE `hBoundaryLim` at the concrete gate, the one genuinely-new fact needed is
  a mass-preserving push-forward / van-Vleck-normalised approximate identity:

      MISSING.  Let `W₀ : Point n → Point n` be the inverse-chart image `z ↦ uniformInverseChart … z 0`
      (a `C¹` diffeomorphism near `0`, `W₀ 0 = 0`, Jacobian `J(z) = |det DW₀(z)|`).  Let
      `amp : ℝ → Point n → ℝ` be the concrete `chartFieldAmp` (bounded, `amp τ · → amp 0 ·` locally
      uniformly as `τ ↓ 0`) with the van-Vleck normalisation `amp 0 0 · J(0)⁻¹ = 1`.  Then for every
      `f : Point n → ℝ` bounded, continuous at `0`, a.e.-measurable,
          `∫ z, gaussDdim τ (W₀ z) · amp τ z · f z  →  f 0`   as `τ ↓ 0`.
      (Type sketch: `Tendsto (fun τ => ∫ z, gaussDdim τ (uniformInverseChart g gi hC hK z 0)
         · chartFieldAmp g gi hC hK a b τ z 0 · f z) (𝓝[>] 0) (𝓝 (f 0))`.)
      Analytic content: change variables `w = W₀ z` (`dz = J(z)⁻¹ dw`), reduce to the BASE-width
      Gaussian approximate identity `GaussianApproxIdentity.gaussDdim_approx_identity`, and use the
      van-Vleck normalisation to cancel `J(0)` against `amp 0 0`.  This is the boundary counterpart of the
      heat-kernel leading-coefficient normalisation; it is the a₁ heat-kernel content itself and does not
      reduce to the wide bank's width-transfer bound.

  a₁ = R/6 remains CONDITIONAL.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.TruncatedDuhamel
import QIQTH.WideSliverBoundary
import QIQTH.WideWitnessAmplitude

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound
open QIQTH.GaussianConvolution QIQTH.ResidueBound
open QIQTH.WideWitnessAmplitude
open scoped Interval Topology BigOperators

namespace QIQTH.WideBoundaryLimDischarge

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (S0) — the zeroth-order per-evaluation wide bound.
    ############################################################################### -/

/-- **★★ (S0) `wide_boundary_inner_bound` — THE ZEROTH-ORDER PER-EVALUATION WIDE BOUND.**  The boundary
    analogue of `WideSliverBoundary.wide_second_inner_slice_bound` (with the `τ⁻¹` endpoint removed).  For
    a kernel `H` wide-dominated at the zeroth order (`|H τ z| ≤ C·gaussDdim (lam·τ) z`, `0 < τ ≤ τ₀`) and
    a width-2-dominated `F` (`|F s z y| ≤ C_L·gaussDdim (2s)(z−y)`), the inner `z`-pairing obeys
        `‖∫ z, H (u−s) z · F s z 0‖ ≤ C·C_L·gaussDdim (lam(u−s)+2s) 0`,
    via the same-point Chapman–Kolmogorov mass `gaussDdim_selfmul_integral` (`∫ G_a·G_b = G_{a+b}(0)`).
    Unlike the second-order slice, there is NO `τ⁻¹`: the resulting envelope is `s`-uniformly bounded.
    NOT `a₁ = R/6`. -/
theorem wide_boundary_inner_bound
    (H : ℝ → Point n → ℝ) (F : ℝ → Point n → Point n → ℝ)
    (lam C C_L T τ₀ : ℝ)
    (hlam : 0 < lam) (hC : 0 ≤ C) (hC_L : 0 ≤ C_L)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z : Point n, |H τ z| ≤ C * gaussDdim (lam * τ) z)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (u s : ℝ) (hspos : 0 < s) (hsT : s ≤ T) (hτpos : 0 < u - s) (hτcap : u - s ≤ τ₀) :
    ‖∫ (z : Point n), H (u - s) z * F s z 0‖
      ≤ C * C_L * gaussDdim (lam * (u - s) + 2 * s) (0 : Point n) := by
  set c : ℝ := C * C_L with hc
  have hdomg : Integrable
      (fun z : Point n => c * (gaussDdim (lam * (u - s)) z * gaussDdim (2 * s) z)) volume :=
    (gaussDdim_selfmul_integrable (lam * (u - s)) (2 * s)).const_mul c
  have hnn : (fun _ : Point n => (0 : ℝ)) ≤ᵐ[volume]
      (fun z : Point n => |H (u - s) z| * |F s z 0|) :=
    ae_of_all _ (fun z => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hle : (fun z : Point n => |H (u - s) z| * |F s z 0|)
      ≤ᵐ[volume]
        (fun z : Point n => c * (gaussDdim (lam * (u - s)) z * gaussDdim (2 * s) z)) := by
    refine ae_of_all _ (fun z => ?_)
    have hA' := hDom (u - s) hτpos hτcap z
    have hB' : |F s z 0| ≤ C_L * gaussDdim (2 * s) z := by
      simpa only [sub_zero] using hFdom s hspos hsT z 0
    have hbnn : 0 ≤ C * gaussDdim (lam * (u - s)) z :=
      mul_nonneg hC (gaussDdim_nonneg _ _)
    calc |H (u - s) z| * |F s z 0|
        ≤ (C * gaussDdim (lam * (u - s)) z) * (C_L * gaussDdim (2 * s) z) :=
          mul_le_mul hA' hB' (abs_nonneg _) hbnn
      _ = c * (gaussDdim (lam * (u - s)) z * gaussDdim (2 * s) z) := by rw [hc]; ring
  calc ‖∫ (z : Point n), H (u - s) z * F s z 0‖
      ≤ ∫ (z : Point n), ‖H (u - s) z * F s z 0‖ := norm_integral_le_integral_norm _
    _ = ∫ (z : Point n), |H (u - s) z| * |F s z 0| := by
        simp only [Real.norm_eq_abs, abs_mul]
    _ ≤ ∫ (z : Point n), c * (gaussDdim (lam * (u - s)) z * gaussDdim (2 * s) z) :=
        integral_mono_of_nonneg hnn hdomg hle
    _ = c * gaussDdim (lam * (u - s) + 2 * s) (0 : Point n) := by
        rw [integral_const_mul, gaussDdim_selfmul_integral (lam * (u - s)) (2 * s)
          (mul_pos hlam hτpos) (by linarith)]

/-! ###############################################################################
    ### (S1) — the `BoundaryTrunc` boundedness member (abstract kernel).
    ############################################################################### -/

/-- **★★ (S1) `wide_boundaryTrunc_bound` — THE BOUNDARY-SEQUENCE ENVELOPE (abstract kernel).**  The
    `BoundaryTrunc` boundary sequence is wide-envelope-dominated:
        `|BoundaryTrunc Wit F m t| ≤ C·C_L·gaussDdim (lam·ε_m + 2(t−ε_m)) 0`,
    from the zeroth wide domination `hDom` of `Wit` at field centre and the width-2 domination `hFdom`.
    Since `BoundaryTrunc Wit F m t = ∫ z, Wit (ε_m) 0 z · F (t−ε_m) z 0` (`t−(t−ε_m)=ε_m`), this is
    `wide_boundary_inner_bound` at `H := Wit · 0 ·`, `u := t`, `s := t−ε_m`.

    ⚠ HONEST SCOPE.  This is the BOUNDEDNESS / tightness member of the boundary pile (the envelope stays
    finite: the width `→ 2t > 0`).  It is NOT the LIMIT-VALUE `hBoundaryLim` (`→ F t 0 0`), which needs
    the chart-image change-of-variables approximate identity (file header (C)).  NOT `a₁ = R/6`. -/
theorem wide_boundaryTrunc_bound
    (Wit F : ℝ → Point n → Point n → ℝ) (lam C C_L T τ₀ : ℝ)
    (hlam : 0 < lam) (hC : 0 ≤ C) (hC_L : 0 ≤ C_L)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z : Point n, |Wit τ 0 z| ≤ C * gaussDdim (lam * τ) z)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (t : ℝ) (m : ℕ) (hst : 0 < t - epsSeq m) (hstT : t - epsSeq m ≤ T) (hεcap : epsSeq m ≤ τ₀) :
    |BoundaryTrunc Wit F m t|
      ≤ C * C_L * gaussDdim (lam * epsSeq m + 2 * (t - epsSeq m)) (0 : Point n) := by
  have hεcancel : t - (t - epsSeq m) = epsSeq m := sub_sub_cancel t (epsSeq m)
  have hb := wide_boundary_inner_bound (fun τ z => Wit τ 0 z) F lam C C_L T τ₀
    hlam hC hC_L hDom hFdom t (t - epsSeq m) hst hstT
    (by rw [hεcancel]; exact epsSeq_pos m)
    (by rw [hεcancel]; exact hεcap)
  -- `hb`'s width/kernel arguments carry `t − (t − ε_m)`; collapse them to `ε_m`.
  rw [hεcancel] at hb
  -- `BoundaryTrunc` is defeq to the integral in `hb`; convert `|·| = ‖·‖`.
  have hBT : BoundaryTrunc Wit F m t
      = ∫ (z : Point n), Wit (epsSeq m) 0 z * F (t - epsSeq m) z 0 := by
    unfold BoundaryTrunc; rw [hεcancel]
  rw [hBT, ← Real.norm_eq_abs]
  exact hb

/-! ###############################################################################
    ### (S2) — the `BoundaryTrunc` boundedness member at the CONCRETE van-Vleck gate.
    ############################################################################### -/

/-- **★★★ (S2) `wide_boundaryTrunc_bound_concrete` — THE CONCRETE-GATE BOUNDARY ENVELOPE.**  The (S1)
    boundary-sequence envelope for the CONCRETE gated van-Vleck witness
    `Wit := vanVleckGatedWitness g gi hC hK S P.D.a P.D.b`, with the zeroth wide domination supplied by
    the wide bank (`WideWitnessAmplitude.WideAmplitudeData.zeroth_domination_global`, needing the honest
    support fact `hSupp`).  For every `m` with `0 < t−ε_m ≤ T` and `ε_m ≤ P.τ₀`,
        `|BoundaryTrunc (vanVleckGatedWitness …) F m t| ≤ C·C_L·gaussDdim (P.D.lam·ε_m + 2(t−ε_m)) 0`.

    This is ONE boundary-pile member (the boundedness / envelope member) discharged AT THE CONCRETE GATE
    VIA THE WIDE BANK.  It is NOT the W1-blocked limit-value member `hBoundaryLim` (see header (B)/(C)).
    NOT `a₁ = R/6`. -/
theorem wide_boundaryTrunc_bound_concrete {g gi : Point n → Fin n → Fin n → ℝ}
    {hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y)}
    {K : Set (Point n)} {hK : IsCompact K} {S : Point n → Set (Point n)} {i : Fin n}
    (P : WideAmplitudeData g gi hC hK S i)
    (hSupp : ∀ z ∈ K, (0 : Point n) ∈ S z → ‖z‖ < P.D.r)
    (F : ℝ → Point n → Point n → ℝ) (C_L T : ℝ) (hC_L : 0 ≤ C_L)
    (hFdom : ∀ s, 0 < s → s ≤ T → ∀ z y : Point n, |F s z y| ≤ C_L * gaussDdim (2 * s) (z - y))
    (t : ℝ) (m : ℕ) (hst : 0 < t - epsSeq m) (hstT : t - epsSeq m ≤ T) (hεcap : epsSeq m ≤ P.τ₀) :
    ∃ C : ℝ, 0 < C ∧
      |BoundaryTrunc (vanVleckGatedWitness g gi hC hK S P.D.a P.D.b) F m t|
        ≤ C * C_L * gaussDdim (P.D.lam * epsSeq m + 2 * (t - epsSeq m)) (0 : Point n) := by
  obtain ⟨C, hCpos, hDom⟩ := P.zeroth_domination_global hSupp
  refine ⟨C, hCpos, ?_⟩
  exact wide_boundaryTrunc_bound (vanVleckGatedWitness g gi hC hK S P.D.a P.D.b) F
    P.D.lam C C_L T P.τ₀
    (zero_lt_one.trans P.D.hlam) hCpos.le hC_L hDom hFdom t m hst hstT hεcap

end QIQTH.WideBoundaryLimDischarge

-- Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound).
#print axioms QIQTH.WideBoundaryLimDischarge.wide_boundary_inner_bound
#print axioms QIQTH.WideBoundaryLimDischarge.wide_boundaryTrunc_bound
#print axioms QIQTH.WideBoundaryLimDischarge.wide_boundaryTrunc_bound_concrete
