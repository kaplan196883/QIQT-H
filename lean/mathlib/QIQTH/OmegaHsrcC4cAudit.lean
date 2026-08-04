/-
  OmegaHsrcC4cAudit — J4-195: two audits + light discharges for the a₁ = R/6 heat-kernel campaign.

  ══════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS IS **NOT** `a₁ = R/6`, and proves NOTHING new about `R/6`.  It is a
  regularity-plumbing + amplitude-structure audit: it (A) rebases the `hsrc` (transport-source)
  smoothness carry of `CapstoneStatus.a1_R6_of_residue` from the unreachable analytic level
  `(⊤ : WithTop ℕ∞) = ω` down to the honest `C^∞` level `∞`, and (B) makes explicit the DIAGONAL
  DeWitt cancellation of the residual amplitude `residualCoeffA`.  No conclusion-in-disguise; no
  vacuous / unsatisfiable hypotheses; NO `sorry`; NO new axioms.  All mains std-3.

  ──────────────────────────────────────────────────────────────────────────────────────────────
  PART A — THE `ω → ∞` `hsrc` AUDIT (a carry removed).

    THE TRACE (verbatim).  `a1_R6_of_residue`'s `hsrc : ContDiff ℝ ⊤ (transportOp (vanVleck g) g gi
    (transportCoeff (transportOp (vanVleck g) g gi) 0))` is consumed by a SINGLE `exact`-chain:
        a1_R6_of_residue
          → trueKernel_diagonal_a1_eq_R6_residual_restricted_C2      (`hsrc` at `⊤`)
            → heatParametrixFn_diagonal_a1_derived                    (`hsrc` at `⊤`)
              → transportCoeff_vanVleck_one_diag                      (`hsrc` at `⊤`)
                → transportCoeff_one_diag                             (`hf`   at `⊤`)
                  → transportCoeff_succ_transport_eq                  (`hf`   at `⊤`)
                    → radialTransportSolve_transport_eq               (`hf`   at `⊤`)  ← ONLY genuine use
    In `radialTransportSolve_transport_eq` (RadialTransport.lean) the smoothness `hf` is used at
    EXACTLY three atoms, EVERY one a strict DOWNCAST:
        • `hf.differentiable (by simp)`         — needs only `C¹`;
        • `hf.continuous`                       — needs only `C⁰`;
        • `continuous_pd f hf i` (= `hf.differentiable` + `hf.continuous_fderiv (by simp)`) — needs `C¹`.
    NO atom uses ANALYTICITY (`ω`).  VERDICT (i): the `⊤` typing of `hsrc` is SPURIOUS throughout —
    it is only ever downcast to `C¹`/`C⁰`.  (Independently corroborated by `HuInftyRebase`'s own
    verdict lines 53–58, and by `radialTransportSolve_contDiff_infty` already living at `∞`.)

    WHAT LANDS.  Because the banked chain is `⊤`-TYPED and `∞` does NOT upcast to `ω`, the safe
    rebase is a genuine RE-THREAD (NOT a coercion).  The single hard rung — the transport ODE
    identity — is FACTORED through its true `C¹` interface `radialTransportSolve_transport_eq_ofC1`
    (weak hypotheses `Differentiable ℝ f` + `∀ i, Continuous (pd f i)`), which BOTH `⊤` and `∞`
    supply.  From it the whole chain is re-threaded to `∞`, culminating in the honest
        • `a1_R6_of_residue_inf` — `CapstoneStatus.a1_R6_of_residue` with `hsrc` at `∞`
          (`ContDiff ℝ (∞ : WithTop ℕ∞) …`), everything else IDENTICAL.
    `hsrc_from_geometry` (InftyRebaseCapstone) delivers exactly this `∞` form from `{hg,hgi,hgpos}`,
    so this rung of the geometry→capstone wiring is now closed at the honest level.  (`hg`/`hgi`/
    `hChr` were already `⊤`-derivable from geometry; only the DERIVED `hsrc` was the wall — now gone.)

  ──────────────────────────────────────────────────────────────────────────────────────────────
  PART B — THE C4c DeWitt-CANCELLATION ASSESSMENT.

    WHERE C4c SITS.  The C4c carry is `hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ t → |heatOp g gi H τ p q|
    ≤ C·baseKernelW 2 0 τ p q` (RestrictedEboundW.trueKernel_diagonal_a1_eq_R6_residual_restricted /
    …_C2).  Its concrete residual is `E = χ·G_τ·A − annulusTerms` with amplitude `A = residualCoeffA`
    (ErrorKernelFactorization).  `residualCoeffA` carries a Laurent head `(1/τ)·[…] + (1/τ²)·[…]`.

    THE STRUCTURE (audited).  Reading `residualCoeffA` (def) against the transport recursion
    (`transportCoeff_succ_transport_eq` — banked) shows the premise "the `1/τ²` and `1/τ` heads
    vanish IDENTICALLY from the recursion" is FALSE as stated: the `1/τ²` head is the pure
    metric-deviation curvature bracket `(-1/4)·∑ᵢⱼ(gⁱʲ−δ)vⁱvʲ · w₀` (residue (I) of
    `parametrixResidual_offdiag_absorbed`) and the `1/τ` head mixes the metric-trace / Christoffel /
    radial-derivative / cross-gradient brackets (residues (I)+(IV)) — these are GENUINE curvature,
    NOT algebraic recursion residuals, and they do NOT vanish off-diagonal.  The repo does NOT cancel
    them: `hEboundW_le` is discharged by GAUSSIAN DOMINATION (polynomial × `G_τ` ≤ width-2 `baseKernelW
    2`, the D1 `gaussDdim((3/2)τ)` estimate, CONDITIONAL on a `GateSqControl` near-isometry
    certificate), NOT by cancellation-to-zero.  The genuine off-diagonal van-Vleck cancellation is the
    Jacobi / exponential-map radial ODE `(r∂_r)log√det g̃ = …` flagged as the shared Mathlib gap in
    `VanVleckCancellation`'s CHECKPOINT — NOT banked.

    WHAT DOES vanish (and IS light): the DIAGONAL.  At the RNC centre `v = 0` (gauge `gⁱʲ(0)=δ`),
    every SINGULAR head of `residualCoeffA` drops out — the `1/τ²` and `1/τ` brackets carry `vⁱ`
    factors or `radialDeriv(·)(0)` (both `0` at the centre), and the `∑(gⁱⁱ(0)−1)` trace vanishes by
    gauge.  This is EXACTLY the diagonal DeWitt cancellation underlying the `radialDeriv_zero`→`R/6`
    chain (Part A).  LANDS as:
        • `residualCoeffA_diag_singular_free` — `residualCoeffA N g gi Θ u t 0` has NO `1/τ`/`1/τ²`
          term: it equals `∑ₖ wₖ(0)·k·τ^{k−1} − ∑ₖ Δ_g(wₖ)(0)·τ^k` (the `∂_τ`-of-`P` minus Laplacian
          part only), given only the RNC gauge `hgi`.
    This honestly separates the (banked, light) diagonal cancellation from the (unbanked, hard)
    off-diagonal Jacobi-field wall.  NOT `a₁ = R/6`.

  Grounded in Rosenberg §3.2.1; Berline–Getzler–Vergne §2.5; Gilkey §1.6/§1.7.  No `sorry`, no new
  axioms.  NOT `a₁ = R/6`.
-/
import Mathlib
import QIQTH.CapstoneStatus
import QIQTH.RadialTransport
import QIQTH.ErrorKernelFactorization

open MeasureTheory
open QIQTH.Curvature QIQTH.LaplaceBeltrami QIQTH.RadialDistance QIQTH.RadialTransport
open QIQTH.ParametrixFunction QIQTH.VanVleck QIQTH.HeatTransportRecursion
open QIQTH.VanVleckCancellation QIQTH.TrueHeatKernel QIQTH.HeatDuhamel QIQTH.LeviSeries
open QIQTH.HeatParametrixAnsatz QIQTH.FlatHeatEquation QIQTH.GaussianWidthTolerant
open QIQTH.HeatResidualBound QIQTH.ErrorKernelFactorization
open scoped BigOperators Topology Interval ContDiff

namespace QIQTH.OmegaHsrcC4cAudit

variable {n : ℕ}

set_option maxHeartbeats 3200000

/-! ══════════════════════════════════════════════════════════════════════════════════════════
    ## PART A — the `ω → ∞` re-thread of the `hsrc` chain.
    ══════════════════════════════════════════════════════════════════════════════════════════ -/

/-! ### A0 — the keystone: the transport ODE identity through its true `C¹` interface.

  `radialTransportSolve_transport_eq` (RadialTransport.lean) is stated at `⊤`, but its proof uses `f`
  ONLY through `Differentiable ℝ f` + `∀ i, Continuous (pd f i)` (see the trace in the header).  We
  re-prove it under exactly those weak hypotheses — verbatim the banked proof with the three `hf`
  atoms replaced by the weak carriers.  BOTH `⊤` and `∞` supply these, so this is the minimal
  interface a future `⊤ → ∞` rebase needs. -/
theorem radialTransportSolve_transport_eq_ofC1 (k : ℕ) (hk : 1 ≤ k) (f : Point n → ℝ)
    (hdiff : Differentiable ℝ f) (hpdc : ∀ i, Continuous (fun x => pd f i x)) (v : Point n) :
    (k : ℝ) * radialTransportSolve k f v + radialDeriv (radialTransportSolve k f) v = f v := by
  have hdiffbl : ∀ x, DifferentiableAt ℝ f x := fun x => hdiff x
  -- `s^{k-1}·s = s^k` for `k ≥ 1`.
  have hpow : ∀ s : ℝ, s ^ (k - 1) * s = s ^ k := fun s => by
    rw [← pow_succ]; congr 1; omega
  -- === Leibniz: the `i`-th partial of `u_k` at `v`. ===
  have hpd : ∀ i : Fin n, pd (radialTransportSolve k f) i v
      = ∫ s in (0:ℝ)..1, s ^ (k - 1) * (s * pd f i (s • v)) := by
    intro i
    -- a uniform bound on `∂ᵢf` over the compact ray tube `[0,1] × closedBall (v i) 1`.
    obtain ⟨M, hM⟩ := (isCompact_Icc.prod (isCompact_closedBall (v i) 1)).exists_bound_of_continuousOn
      (f := fun p : ℝ × ℝ => pd f i (p.1 • Function.update v i p.2))
      ((hpdc i).comp
        (continuous_fst.smul ((continuous_updatePt v i).comp continuous_snd))).continuousOn
    -- continuity of the integrand and its parameter-derivative.
    have hcF : ∀ t : ℝ, Continuous (fun s : ℝ => s ^ (k - 1) * f (s • Function.update v i t)) :=
      fun t => (continuous_pow (k - 1)).mul (hdiff.continuous.comp (continuous_id.smul continuous_const))
    have hcF' : ∀ t : ℝ,
        Continuous (fun s : ℝ => s ^ (k - 1) * (s * pd f i (s • Function.update v i t))) :=
      fun t => (continuous_pow (k - 1)).mul (continuous_id.mul
        ((hpdc i).comp (continuous_id.smul continuous_const)))
    -- the dominating bound.
    have hbound : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι (0:ℝ) 1 →
        ∀ t ∈ Metric.ball (v i) 1,
          ‖s ^ (k - 1) * (s * pd f i (s • Function.update v i t))‖ ≤ (fun _ => M) s := by
      refine Filter.Eventually.of_forall (fun s hs t ht => ?_)
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
      obtain ⟨hs0, hs1⟩ := hs
      have hmem : (s, t) ∈ Set.Icc (0:ℝ) 1 ×ˢ Metric.closedBall (v i) 1 :=
        ⟨⟨le_of_lt hs0, hs1⟩, Metric.ball_subset_closedBall ht⟩
      have hb := hM (s, t) hmem
      rw [Real.norm_eq_abs] at hb ⊢
      rw [abs_mul, abs_mul]
      have h1 : |s ^ (k - 1)| ≤ 1 := by
        rw [abs_of_nonneg (by positivity)]; exact pow_le_one₀ (le_of_lt hs0) hs1
      have h2 : |s| ≤ 1 := by rw [abs_of_nonneg (le_of_lt hs0)]; exact hs1
      have hpdnn : (0:ℝ) ≤ |pd f i (s • Function.update v i t)| := abs_nonneg _
      have step : |s| * |pd f i (s • Function.update v i t)| ≤ M :=
        le_trans (mul_le_mul h2 hb hpdnn (by norm_num)) (le_of_eq (one_mul M))
      calc |s ^ (k - 1)| * (|s| * |pd f i (s • Function.update v i t)|)
          ≤ 1 * M := mul_le_mul h1 step (by positivity) (by norm_num)
        _ = M := one_mul M
    -- the pointwise `t`-derivative.
    have hderiv : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ι (0:ℝ) 1 →
        ∀ t ∈ Metric.ball (v i) 1,
          HasDerivAt (fun t => s ^ (k - 1) * f (s • Function.update v i t))
            (s ^ (k - 1) * (s * pd f i (s • Function.update v i t))) t := by
      refine Filter.Eventually.of_forall (fun s _ t _ => ?_)
      have hup : HasDerivAt (fun t => s • Function.update v i t) (s • Pi.single i 1) t :=
        (hasDerivAt_update v i t).const_smul s
      have hff : HasFDerivAt f (fderiv ℝ f (s • Function.update v i t))
          (s • Function.update v i t) := (hdiffbl _).hasFDerivAt
      have hcomp := hff.comp_hasDerivAt t hup
      have hval : (fderiv ℝ f (s • Function.update v i t)) (s • Pi.single i 1)
          = s * pd f i (s • Function.update v i t) := by
        rw [map_smul, smul_eq_mul, ← pd_eq_fderiv f i (s • Function.update v i t) (hdiffbl _)]
      rw [hval] at hcomp
      exact HasDerivAt.const_mul (s ^ (k - 1)) hcomp
    -- apply the parametric Leibniz rule.
    have leibniz := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun t s => s ^ (k - 1) * f (s • Function.update v i t))
      (F' := fun t s => s ^ (k - 1) * (s * pd f i (s • Function.update v i t)))
      (bound := fun _ => M) (x₀ := v i) (s := Metric.ball (v i) 1) (a := 0) (b := 1)
      (Metric.ball_mem_nhds (v i) one_pos)
      (Filter.Eventually.of_forall (fun t => (hcF t).aestronglyMeasurable))
      ((hcF (v i)).intervalIntegrable 0 1)
      ((hcF' (v i)).aestronglyMeasurable)
      hbound intervalIntegrable_const hderiv
    -- read off `pd u_k i v`, rewriting `update v i (v i) = v`.
    have h0 : HasDerivAt
        (fun t => ∫ s in (0:ℝ)..1, s ^ (k - 1) * f (s • Function.update v i t))
        (∫ s in (0:ℝ)..1, s ^ (k - 1) * (s * pd f i (s • v))) (v i) := by
      have := leibniz.2
      rw [show (∫ s in (0:ℝ)..1, s ^ (k - 1) * (s * pd f i (s • Function.update v i (v i))))
            = ∫ s in (0:ℝ)..1, s ^ (k - 1) * (s * pd f i (s • v)) from
          intervalIntegral.integral_congr (fun s _ => by rw [Function.update_eq_self])] at this
      exact this
    have hval2 : deriv (fun t => radialTransportSolve k f (Function.update v i t)) (v i)
        = ∫ s in (0:ℝ)..1, s ^ (k - 1) * (s * pd f i (s • v)) := h0.deriv
    rw [pd]; exact hval2
  -- === radialDeriv u_k as a single ray integral. ===
  have hRD : radialDeriv (radialTransportSolve k f) v
      = ∫ s in (0:ℝ)..1, s ^ k * (∑ i, v i * pd f i (s • v)) := by
    rw [radialDeriv]
    have hswap : ∀ i, v i * pd (radialTransportSolve k f) i v
        = ∫ s in (0:ℝ)..1, v i * (s ^ (k - 1) * (s * pd f i (s • v))) := by
      intro i; rw [hpd i, ← intervalIntegral.integral_const_mul]
    have hInt : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        IntervalIntegrable (fun s => v i * (s ^ (k - 1) * (s * pd f i (s • v)))) volume 0 1 :=
      fun i _ => (continuous_const.mul ((continuous_pow (k - 1)).mul (continuous_id.mul
        ((hpdc i).comp (continuous_id.smul continuous_const))))).intervalIntegrable 0 1
    rw [Finset.sum_congr rfl (fun i _ => hswap i), ← intervalIntegral.integral_finsetSum hInt]
    apply intervalIntegral.integral_congr
    intro s _
    show (∑ i, v i * (s ^ (k - 1) * (s * pd f i (s • v))))
        = s ^ k * ∑ i, v i * pd f i (s • v)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hpow s]; ring
  -- === integration by parts. ===
  have hv'int : IntervalIntegrable (fun s => ∑ i, v i * pd f i (s • v)) volume 0 1 :=
    (continuous_finsetSum Finset.univ (fun i _ => continuous_const.mul
      ((hpdc i).comp (continuous_id.smul continuous_const)))).intervalIntegrable 0 1
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun s : ℝ => s ^ k) (v := fun s => f (s • v))
    (u' := fun s => (k : ℝ) * s ^ (k - 1)) (v' := fun s => ∑ i, v i * pd f i (s • v))
    (fun s _ => hasDerivAt_pow k s)
    (fun s _ => hasDerivAt_ray f v s (hdiffbl _))
    ((continuous_const.mul (continuous_pow (k - 1))).intervalIntegrable 0 1)
    hv'int
  have hInt2 : (∫ s in (0:ℝ)..1, ((k : ℝ) * s ^ (k - 1)) * f (s • v))
      = (k : ℝ) * radialTransportSolve k f v := by
    rw [radialTransportSolve, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _; ring
  rw [hRD, hIBP, hInt2]
  simp only [one_pow, one_smul, one_mul, zero_pow (show k ≠ 0 by omega), zero_mul, sub_zero]
  ring

/-! ### A1 — the `∞` rungs, re-threaded through A0. -/

/-- `∞` mirror of `RadialTransport.continuous_pd`. -/
theorem continuous_pd_infty (f : Point n → ℝ) (hf : ContDiff ℝ (∞ : WithTop ℕ∞) f) (i : Fin n) :
    Continuous (fun x => pd f i x) :=
  (contDiff_pd_inf f hf i).continuous

/-- `∞` mirror of `RadialTransport.radialTransportSolve_transport_eq`. -/
theorem radialTransportSolve_transport_eq_infty (k : ℕ) (hk : 1 ≤ k) (f : Point n → ℝ)
    (hf : ContDiff ℝ (∞ : WithTop ℕ∞) f) (v : Point n) :
    (k : ℝ) * radialTransportSolve k f v + radialDeriv (radialTransportSolve k f) v = f v :=
  radialTransportSolve_transport_eq_ofC1 k hk f (hf.differentiable (by simp))
    (fun i => continuous_pd_infty f hf i) v

/-- `∞` mirror of `ParametrixFunction.transportCoeff_succ_transport_eq`. -/
theorem transportCoeff_succ_transport_eq_infty (T : (Point n → ℝ) → (Point n → ℝ)) (k : ℕ)
    (hf : ContDiff ℝ (∞ : WithTop ℕ∞) (T (transportCoeff T k))) (v : Point n) :
    ((k : ℝ) + 1) * transportCoeff T (k + 1) v
      + radialDeriv (transportCoeff T (k + 1)) v = T (transportCoeff T k) v := by
  have h := radialTransportSolve_transport_eq_infty (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
    (T (transportCoeff T k)) hf v
  rw [transportCoeff_succ]
  rw [Nat.cast_add, Nat.cast_one] at h
  exact h

/-- `∞` mirror of `VanVleckCancellation.transportCoeff_one_diag`. -/
theorem transportCoeff_one_diag_infty (T : (Point n → ℝ) → (Point n → ℝ))
    (hf : ContDiff ℝ (∞ : WithTop ℕ∞) (T (transportCoeff T 0))) :
    transportCoeff T 1 (0 : Point n) = T (transportCoeff T 0) (0 : Point n) := by
  have h := transportCoeff_succ_transport_eq_infty T 0 hf (0 : Point n)
  rw [radialDeriv_zero] at h
  simpa using h

/-- `∞` mirror of `VanVleckCancellation.transportCoeff_vanVleck_one_diag`. -/
theorem transportCoeff_vanVleck_one_diag_infty (g gi : Point n → Fin n → Fin n → ℝ)
    (Ric : Fin n → Fin n → ℝ)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0))) :
    transportCoeff (transportOp (vanVleck g) g gi) 1 (0 : Point n) = (∑ i, Ric i i) / 6 := by
  rw [transportCoeff_one_diag_infty (transportOp (vanVleck g) g gi) hsrc, transportCoeff_zero]
  exact transportSource_diag_eq_scalarCurv g gi Ric hg hg0 hgi hΓ hdg0 htr

/-- ★ `∞` mirror of `VanVleckCancellation.heatParametrixFn_diagonal_a1_derived`.  The van-Vleck
    parametrix diagonal `a₁ = R/6` expansion with the transport-source smoothness at the HONEST `∞`
    level (what `hsrc_from_geometry` supplies) rather than the unreachable analytic `⊤`. -/
theorem heatParametrixFn_diagonal_a1_derived_infty (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ)
    (Ric : Fin n → Fin n → ℝ) (t : ℝ) (hN : 1 ≤ N)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0))) :
    heatParametrixFn N g (transportOp (vanVleck g) g gi) t (0 : Point n)
      = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
        * (1 + ((∑ i, Ric i i) / 6) * t
            + ∑ k ∈ Finset.Ico 2 (N + 1),
                transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n) * t ^ k) := by
  have hdet0 : Matrix.det (g 0) = 1 := by
    have hg0mat : g 0 = (1 : Matrix (Fin n) (Fin n) ℝ) := by funext i j; exact hg0 i j
    rw [hg0mat, Matrix.det_one]
  exact heatParametrixFn_diagonal_a1 N g (transportOp (vanVleck g) g gi) t (∑ i, Ric i i) hdet0 hN
    (transportCoeff_vanVleck_one_diag_infty g gi Ric hg hg0 hgi hΓ hdg0 htr hsrc)

/-! ### A2 — the true-kernel `_C2` capstone and `a1_R6_of_residue`, re-threaded to `∞`.

  Verbatim copies of `ConcreteDominations.trueKernel_diagonal_a1_eq_R6_residual_restricted_C2` and
  `CapstoneStatus.a1_R6_of_residue`, with the SINGLE `hsrc`-consuming call swapped to its `∞` mirror.
  Every other hypothesis is unchanged (`hg`/`hgi`/`hChr` stay at `⊤` — geometry supplies them). -/

/-- `∞`-`hsrc` mirror of `ConcreteDominations.trueKernel_diagonal_a1_eq_R6_residual_restricted_C2`. -/
theorem trueKernel_diagonal_a1_eq_R6_residual_restricted_C2_infty
    (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : 0 < t)
    (H : ℝ → Point n → Point n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ a b, ContDiff ℝ ⊤ (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hHdiag : H t 0 0 = heatParametrixFn N g (transportOp (vanVleck g) g gi) t (0 : Point n))
    (hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi H τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hInt : IterConvIntegrableW (heatOp g gi H) 2 0 C)
    (hDuhamel : heatOp g gi (fun u p q => heatConv H (leviSeries (heatOp g gi H)) u p q) t 0 0
        = leviSeries (heatOp g gi H) t 0 0
          + heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0)
    (hInter : heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0
        = ∑' k : ℕ, heatConv (heatOp g gi H)
            (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE (heatOp g gi H) (k + 1) τ p q) t 0 0)
    (hDH : DifferentiableAt ℝ (fun u => H u 0 0) t)
    (hDConv : DifferentiableAt ℝ (fun u => heatConv H (leviSeries (heatOp g gi H)) u 0 0) t)
    (hCH : ContDiffAt ℝ 2 (fun p => H t p 0) (0 : Point n))
    (hCConv : ContDiffAt ℝ 2 (fun p => heatConv H (leviSeries (heatOp g gi H)) t p 0) (0 : Point n)) :
    heatOp g gi (trueHeatKernel H (leviSeries (heatOp g gi H))) t 0 0 = 0
    ∧ trueHeatKernel H (leviSeries (heatOp g gi H)) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, Ric i i) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (N + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv H (leviSeries (heatOp g gi H)) t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  have hpref : (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n ≠ 0 :=
    pow_ne_zero n (ne_of_gt (QIQTH.GaussianConvolution.heatKernel1D_pos t 0 ht))
  have ht2 : (t : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt ht)
  have hIterSum := neumann_summable_alpha0_width2_le (heatOp g gi H) C hC t
    hEboundW_le hInt t ht le_rfl (0 : Point n) (0 : Point n)
  have hSum : Summable
      (fun k : ℕ => (-1 : ℝ) ^ (k + 1) * iterE (heatOp g gi H) (k + 1) t (0 : Point n) (0 : Point n)) := by
    have habs : Summable
        (fun k : ℕ => |iterE (heatOp g gi H) (k + 1) t (0 : Point n) (0 : Point n)|) :=
      summable_abs_iff.mpr hIterSum
    refine Summable.of_norm_bounded habs (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    simp
  have hHeat : heatOp g gi (trueHeatKernel H (leviSeries (heatOp g gi H))) t 0 0 = 0 :=
    trueHeatKernel_heat_eqn_levi_C2 g gi H (heatOp g gi H) t 0 0 rfl hDuhamel hSum hInter
      hDH hDConv hCH hCConv
  have hParam := heatParametrixFn_diagonal_a1_derived_infty N g gi Ric t hN hg hg0 hgi hΓ hdg0 htr hsrc
  have htail_eq : (∑ k ∈ Finset.Ico 2 (N + 1),
        transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n) * t ^ k)
      = t ^ 2 * ∑ k ∈ Finset.Ico 2 (N + 1),
        transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n) * t ^ (k - 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
    have hpow : t ^ 2 * t ^ (k - 2) = t ^ k := by
      rw [← pow_add]; congr 1; omega
    rw [← hpow]; ring
  have hExp : trueHeatKernel H (leviSeries (heatOp g gi H)) t 0 0
      = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
        * (1 + ((∑ i, Ric i i) / 6) * t
            + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (N + 1),
                        transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                          * t ^ (k - 2))
                      + heatConv H (leviSeries (heatOp g gi H)) t 0 0
                          / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
    rw [trueHeatKernel_apply, hHdiag, hParam, htail_eq]
    field_simp
    ring
  exact ⟨hHeat, hExp⟩

/-- ★★ `a1_R6_of_residue_inf` — `CapstoneStatus.a1_R6_of_residue` with the `hsrc` (transport-source)
    carry at the HONEST `C^∞` level `∞` instead of the unreachable analytic `⊤`.  Everything else is
    byte-for-byte identical to the banked capstone; the `∞`-typed `hsrc` is EXACTLY what
    `InftyRebaseCapstone.hsrc_from_geometry` delivers from `{hg, hgi, hgpos}`.  NOT `a₁ = R/6`. -/
theorem a1_R6_of_residue_inf (g gi : Point n → Fin n → Fin n → ℝ) (Ric : Fin n → Fin n → ℝ)
    (t : ℝ) (ht : 0 < t) (C : ℝ) (hCnn : 0 ≤ C)
    (hChr : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (S : Point n → Set (Point n)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hK0 : (0 : Point n) ∈ K) (hS0 : (0 : Point n) ∈ S 0)
    (H : ℝ → Point n → Point n → ℝ)
    (hHeq : H = vanVleckGatedWitness g gi hChr hK S a b)
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hg0 : ∀ i j, g 0 i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0)
    (hΓ : ∀ k i j, christoffel g gi k i j (0 : Point n) = 0)
    (hdg0 : ∀ a b e, pd (fun y => g y a b) e 0 = 0)
    (htr : ∀ c d, (∑ a, pd (fun y => pd (fun w => g w a a) d y) c 0) = -(2 / 3) * Ric c d)
    (hsrc : ContDiff ℝ (∞ : WithTop ℕ∞)
      (transportOp (vanVleck g) g gi (transportCoeff (transportOp (vanVleck g) g gi) 0)))
    (hEboundW_le : ∀ τ p q, 0 < τ → τ ≤ t →
        |heatOp g gi H τ p q| ≤ C * baseKernelW (2 : ℝ) (0 : ℝ) τ p q)
    (hInt : IterConvIntegrableW (heatOp g gi H) 2 0 C)
    (hDuhamel : heatOp g gi (fun u p q => heatConv H (leviSeries (heatOp g gi H)) u p q) t 0 0
        = leviSeries (heatOp g gi H) t 0 0
          + heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0)
    (hInter : heatConv (heatOp g gi H) (leviSeries (heatOp g gi H)) t 0 0
        = ∑' k : ℕ, heatConv (heatOp g gi H)
            (fun τ p q => (-1 : ℝ) ^ (k + 1) * iterE (heatOp g gi H) (k + 1) τ p q) t 0 0)
    (hDConv : DifferentiableAt ℝ (fun u => heatConv H (leviSeries (heatOp g gi H)) u 0 0) t)
    (hCH : ContDiffAt ℝ 2 (fun p => H t p 0) (0 : Point n))
    (hCConv : ContDiffAt ℝ 2 (fun p => heatConv H (leviSeries (heatOp g gi H)) t p 0) (0 : Point n)) :
    heatOp g gi (trueHeatKernel H (leviSeries (heatOp g gi H))) t 0 0 = 0
    ∧ trueHeatKernel H (leviSeries (heatOp g gi H)) t 0 0
        = (QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n
          * (1 + ((∑ i, Ric i i) / 6) * t
              + t ^ 2 * ((∑ k ∈ Finset.Ico 2 (1 + 1),
                          transportCoeff (transportOp (vanVleck g) g gi) k (0 : Point n)
                            * t ^ (k - 2))
                        + heatConv H (leviSeries (heatOp g gi H)) t 0 0
                            / ((QIQTH.HeatKernelA1.heatKernel1D t 0) ^ n * t ^ 2))) := by
  subst hHeq
  have hHdiag : vanVleckGatedWitness g gi hChr hK S a b t 0 0
      = heatParametrixFn 1 g (transportOp (vanVleck g) g gi) t (0 : Point n) :=
    capstone_hHdiag_supplied g gi hChr hK S a b ha hab t hK0 hS0
  have hDH : DifferentiableAt ℝ (fun u => vanVleckGatedWitness g gi hChr hK S a b u 0 0) t :=
    capstone_hDH_supplied g gi hChr hK S a b ha hab t ht hK0 hS0
  exact trueKernel_diagonal_a1_eq_R6_residual_restricted_C2_infty g gi Ric 1 le_rfl t ht
    (vanVleckGatedWitness g gi hChr hK S a b) C hCnn hg hg0 hgi hΓ hdg0 htr hsrc
    hHdiag hEboundW_le hInt hDuhamel hInter hDH hDConv hCH hCConv

/-! ══════════════════════════════════════════════════════════════════════════════════════════
    ## PART B — the C4c diagonal DeWitt-cancellation lemma.
    ══════════════════════════════════════════════════════════════════════════════════════════ -/

/-- ★ `residualCoeffA_diag_singular_free` — at the RNC centre `v = 0` (gauge `gⁱʲ(0) = δ`), the
    Seeley–DeWitt residual amplitude `residualCoeffA` has NO `1/τ` or `1/τ²` singular term.  Every
    singular head carries either a `vⁱ` factor (Christoffel / metric-deviation / cross-gradient
    brackets), a `radialDeriv(·)(0)` (all `0` by `radialDeriv_zero`), or the metric trace
    `∑ᵢ(gⁱⁱ(0) − 1) = 0` (gauge).  What survives is exactly the `∂_τ`-of-`P` minus the Laplacian
    part:
        `residualCoeffA N g gi Θ u τ 0 = ∑ₖ wₖ(0)·k·τ^{k−1} − ∑ₖ Δ_g(wₖ)(0)·τ^k`.
    This is the DIAGONAL DeWitt cancellation (the `v = 0` face of the van-Vleck leading transport ODE)
    — the light, banked half; the OFF-diagonal cancellation is the Jacobi/exp-map wall (NOT here).
    NOT `a₁ = R/6`. -/
theorem residualCoeffA_diag_singular_free (N : ℕ) (g gi : Point n → Fin n → Fin n → ℝ)
    (Θ : Point n → ℝ) (u : ℕ → Point n → ℝ) (t : ℝ)
    (hgi : ∀ i j, gi (0 : Point n) i j = if i = j then 1 else 0) :
    residualCoeffA N g gi Θ u t (0 : Point n)
      = (∑ k ∈ Finset.range (N + 1), foldedCoeff Θ u k 0 * ((k : ℝ) * t ^ (k - 1)))
        - (∑ k ∈ Finset.range (N + 1), laplaceBeltrami g gi (foldedCoeff Θ u k) 0 * t ^ k) := by
  have htrace : (∑ i, (gi (0 : Point n) i i - 1)) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [hgi i i]; simp
  have hrd0 : radialDeriv (foldedCoeff Θ u 0) (0 : Point n) = 0 := radialDeriv_zero _
  have hrdsum : (∑ k ∈ Finset.range N,
      radialDeriv (foldedCoeff Θ u (k + 1)) (0 : Point n) * t ^ k) = 0 := by
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [radialDeriv_zero]; ring
  simp only [residualCoeffA, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero,
    zero_add, add_zero, sub_zero, htrace, hrd0, hrdsum]

end QIQTH.OmegaHsrcC4cAudit

section AxiomChecks
open QIQTH.OmegaHsrcC4cAudit
#print axioms radialTransportSolve_transport_eq_ofC1
#print axioms radialTransportSolve_transport_eq_infty
#print axioms heatParametrixFn_diagonal_a1_derived_infty
#print axioms trueKernel_diagonal_a1_eq_R6_residual_restricted_C2_infty
#print axioms a1_R6_of_residue_inf
#print axioms residualCoeffA_diag_singular_free
end AxiomChecks
