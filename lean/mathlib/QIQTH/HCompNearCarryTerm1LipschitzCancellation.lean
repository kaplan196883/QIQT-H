/-
  HCompNearCarryTerm1LipschitzCancellation — J4-1019: the G1 gate — a SIGNED, pre-`|·|` combined
  Lipschitz-weighted bound on `nb`'s `Bfac` term1, composing J4-1017's (G3) exact algebraic identity
  with J4-998's (`HeatHessianMomentCancellation`) already-banked `heatHessMult` cancellation-then-
  Lipschitz payoff AND a new analogous cancellation-then-Lipschitz payoff for the leftover linear
  (`linMult`) piece J4-1017 exposed (per Sol `gpt-5.6-sol`'s staged G3/G2/G1 plan, cp902–cp905).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## THE PROBLEM (Sol's own framing of G1, the HIGHEST-RISK gate).  If a naive proof bounds
  `|hsMixed·G_τ(U)·Amp(U)|` (or the whole `kPrime`/`Bfac` integrand) with absolute values FIRST and
  only THEN tries to integrate, the moment cancellation `integral_heatHessMult_eq_zero` is DESTROYED
  (`∫|f|` does not benefit from sign cancellation the way `|∫f|` does).  G1's job is to expose BOTH
  cancellations — the Hessian piece (J4-998) AND the leftover first-moment piece (J4-1017's residual
  `−⟨U,Q⟩/(2τ)·G_τ(U)`) — as SIGNED integrals, combine them via J4-1017's exact algebraic identity,
  and take `|·|` only at the VERY END, on the fully-assembled combined bound.

  ## THE ASSEMBLY.  J4-1017's exact `ring` identity is
      `hsMixed(τ,U,PI,PJ,Q) · G_τ(U) = heatHessMult τ PI PJ U − linMult τ Q U`,
  where THIS FILE introduces `linMult τ Q v := (⟨v,Q⟩/(2τ)) · G_τ(v)` — literally J4-1017's residual
  term as a standalone n-D Gaussian-linear multiplier, in EXACT analogy to `heatHessMult`.  Just as
  `heatHessMult` has an EXACT full-space zero integral (`integral_heatHessMult_eq_zero`, J4-998, via
  the M0/M2 moments) and a Lipschitz-remainder payoff (`integral_heatHessMult_mul_lipschitz`, O(1/√τ)),
  `linMult` has its OWN exact full-space zero integral (`integral_linMult_eq_zero`, via the ALREADY-
  BANKED M1 oddness moment `GaussianMomentExtraction.gaussDdim_first_moment_zero` — pure linearity,
  no new moment machinery) and its OWN Lipschitz-remainder payoff (`integral_linMult_mul_lipschitz`),
  built here by the SAME cancellation-then-remainder route as `heatHessMult`'s, landing at a bound that
  is CONSTANT in `τ` (the `τ`'s cancel exactly — sympy-verified, part of why this is safe: it does not
  threaten the `O(1/√τ)` rate `heatHessMult` delivers, it decays FASTER when integrated over a `τ`-
  sliver).  The combined theorem `hsMixed_gaussDdim_mul_amp_lipschitz_bound` derives the two SIGNED
  cancellation-then-remainder integrals FIRST (via `integral_sub` on the centred integrand, exactly as
  Sol's audit specifies — see the intermediate identity below), and only THEN applies the triangle
  inequality to the two ALREADY-BOUNDED pieces — i.e. `|A − B| ≤ |A| + |B|` where `A` and `B` are each
  themselves the OUTPUT of a sign-preserving cancellation argument, not the raw un-cancelled integrand.
  This is genuinely G1's intent (Sol `gpt-5.6-sol`, high, 2026-08-23, consulted with the sympy rate
  check BEFORE this file: "the required cancellation is exposed separately in each signed integral
  … applying the triangle inequality only after these rewrites does not destroy cancellation").

  The auditable intermediate identity (banked as `hsMixed_gaussDdim_mul_amp_eq_diff` below,
  BEFORE any `|·|`):
      `∫ v, G_τ(v)·(hsMixed(τ,v,PI,PJ,Q)·Amp v)
          = (∫ v, heatHessMult τ PI PJ v · Amp v)
              − (∫ v, linMult τ Q v · Amp v)`,
  which then gets bounded (via `integral_heatHessMult_mul_lipschitz` and the new
  `integral_linMult_mul_lipschitz`, each applied DIRECTLY to the full-`Amp` integral — both already
  perform their OWN internal sign-cancellation-then-remainder split before bounding) to
      `|∫ v, G_τ(v)·(hsMixed(τ,v,PI,PJ,Q)·Amp v)|
          ≤ L·n³·‖PI‖·‖PJ‖·(16√2+1)/√τ + n²·L·‖Q‖`
  for `Amp` Lipschitz-at-`0` with modulus `L`.

  ## SYMPY VERIFICATION (`docs/qg_roadmap/rnc_sympy/hcomp_g1_term1_combined_rate_check.py`, BEFORE
  this file): (1) the `linMult` Lipschitz-remainder bound is EXACTLY `n²·L·‖Q‖` — the `τ` dependence
  cancels identically between the `1/(2τ)` prefactor and the `k=2` moment envelope's `O(τ)` growth;
  (2) integrating the WORST-CASE combined bound `C1/√τ + C2` over the sliver `τ ∈ (0,ε)` gives
  `2·C1·√ε + C2·ε`, and `C2·ε = o(√ε)` as `ε → 0⁺` (verified via the limit `(C2ε)/√ε → 0`) — i.e. the
  `linMult` piece is GENUINELY NEGLIGIBLE against the `O(√ε)` target rate `heatHessMult`'s own Lipschitz
  payoff already delivers; it does NOT worsen the rate `hcomp`'s `nb` needs.

  ## WHAT LANDS.
    • `linMult` — the n-D Gaussian-linear multiplier `(⟨v,Q⟩/(2τ))·G_τ(v)`, literally J4-1017's residual
      term as a standalone object.
    • `integral_linMult_eq_zero` — the exact full-space zero integral (via `gaussDdim_first_moment_zero`
      and linearity of the finite sum `⟨v,Q⟩ = ∑ v_k Q_k`).
    • `linMult_integrable` — integrability of `linMult`.
    • `abs_linMult_le` — the pointwise majorant `|linMult τ Q v| ≤ (n‖Q‖/(2τ))·‖v‖·G_τ(v)`.
    • `integral_linMult_mul_lipschitz` — ★ the `linMult` Lipschitz-remainder payoff, mirroring
      `integral_heatHessMult_mul_lipschitz`'s EXACT proof shape: `|∫ v, linMult τ Q v · f v| ≤
      n²·L·‖Q‖` (CONSTANT in `τ`).
    • `heatHessMult_mul_lipschitzAmp_integrable` / `linMult_mul_lipschitzAmp_integrable` — integrability
      helpers for the full-`Amp`-weighted products (needed by `integral_sub` below), via the
      `Amp = (Amp − Amp 0) + Amp 0` split.
    • `hsMixed_gaussDdim_mul_amp_eq_diff` — the AUDITABLE intermediate SIGNED identity
      (pre-`|·|`), rewriting the full-space `hsMixed·G_τ·Amp` integral as the DIFFERENCE of the two
      full-`Amp` integrals, via J4-1017's algebraic identity + `integral_sub` — the literal "expose the
      cancellation before `|·|`" step G1 demands.
    • `hsMixed_gaussDdim_mul_amp_lipschitz_bound` — ★★★ THE G1 PAYOFF: composing the above with
      `integral_heatHessMult_mul_lipschitz` and `integral_linMult_mul_lipschitz`, the combined SIGNED-
      THEN-BOUNDED estimate
      `|∫ v, G_τ(v)·(hsMixed(τ,v,PI,PJ,Q)·Amp v)| ≤ L·n³·‖PI‖·‖PJ‖·(16√2+1)/√τ + n²·L·‖Q‖`.

  ⚠  HONESTY FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  DECOUPLED, FULL-SPACE (`ℝⁿ`, not the opaque IFT domain `S'`) analysis result — same status as J4-998
  and J4-1018 themselves.  It does NOT touch domain restriction: reconciling this full-space bound with
  `nb`'s actual bounded post-CoV domain `S'` (the r3/r4 residuals — does `S'` contain a concrete ball?)
  and combining with J4-1018's `heatHessMult_ball_tail_le` ball-tail bound (which itself needs an
  analogous `linMult` ball-tail companion, NOT built here) is SEPARATE, still-open work, EXPLICITLY
  NOT attempted here.  `Amp` here stands in for `chartFieldAmp g gi hC hK a b (t−s) z x` composed with
  the inverse chart map `V` from `HCompNearCarryKPrimeBaseFieldCoV`'s CoV (BRICK 2) — whether THAT
  composite is genuinely Lipschitz-at-a-point is itself an UNVERIFIED hypothesis here, supplied
  abstractly (`Amp`, `AEStronglyMeasurable`, Lipschitz modulus `L`), NOT discharged for the literal
  chart amplitude.  Sol's own G1 caveat: "do not hide domain restriction inside `Amp`: an indicator
  generally destroys Lipschitzness" — no indicator/cutoff is used here, `Amp` is a genuine full-space
  weight.  This file does NOT discharge `nb`, `hCConv`, or any part of `hcomp`; it does NOT discharge
  the OTHER 3 terms of `Bfac`'s 4-term sum (only term1/`hsMixed` is addressed); the far-carry `fb`
  remains SEPARATELY open regardless.  `a₁ = R/6` remains STRICTLY CONDITIONAL on
  `{hDuhamel, hDConv, hCConv}`, UNCHANGED.  NOT `a₁ = R/6`.  No `sorry`, no new axioms, no `:= True`,
  no vacuous / unsatisfiable hypothesis, none equal to the conclusion (the combined bound is a genuine
  new quantitative estimate, not a restatement of either banked piece), no existing file edited.
  ══════════════════════════════════════════════════════════════════════════════════════════════════
-/
import Mathlib
import QIQTH.HeatHessianMomentCancellation
import QIQTH.GaussianMomentExtraction

open MeasureTheory Filter Set
open QIQTH.Curvature QIQTH.HeatKernelA1 QIQTH.FlatHeatEquation QIQTH.GaussianConvolution
open QIQTH.HeatResidualBound QIQTH.ResidueBound QIQTH.HeatHessMoment
open scoped Topology BigOperators

namespace QIQTH.HCompNearCarryTerm1LipschitzCancellation

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### 1. `linMult` — J4-1017's residual first-moment term, as a standalone n-D multiplier.
    ############################################################################### -/

/-- **The n-D heat-kernel linear multiplier.**  `linMult τ Q v := (⟨v,Q⟩/(2τ))·G_τ(v)`, literally
    J4-1017's residual `−⟨U,Q⟩/(2τ)·G_τ(U)` term (up to the overall sign carried at the use site) as
    a standalone object, in exact analogy to `heatHessMult`. -/
noncomputable def linMult (τ : ℝ) (Q v : Point n) : ℝ :=
  (∑ k, v k * Q k) / (2 * τ) * gaussDdim τ v

/-- `|⟨v,p⟩| ≤ n·‖v‖·‖p‖` for the sup norm on `Point n` (local restatement of
    `HeatHessMoment.abs_dot_le`, which is `private` there). -/
private theorem abs_dot_le' (v p : Point n) : |∑ k, v k * p k| ≤ (n : ℝ) * ‖v‖ * ‖p‖ := by
  calc |∑ k, v k * p k| ≤ ∑ k, |v k * p k| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |v k| * |p k| := by simp only [abs_mul]
    _ ≤ ∑ _k : Fin n, ‖v‖ * ‖p‖ := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        exact mul_le_mul (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v k)
          (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm p k) (abs_nonneg _) (norm_nonneg _)
    _ = (n : ℝ) * ‖v‖ * ‖p‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

/-- `linMult τ Q ·` is integrable. -/
theorem linMult_integrable (τ : ℝ) (hτ : 0 < τ) (Q : Point n) :
    Integrable (fun v : Point n => linMult τ Q v) volume := by
  have hd_int : Integrable (fun v : Point n => (∑ k, v k * Q k) * gaussDdim τ v) volume := by
    have hpt : (fun v : Point n => (∑ k, v k * Q k) * gaussDdim τ v)
        = fun v => ∑ k, Q k * (gaussDdim τ v * v k) := by
      funext v
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [hpt]
    exact integrable_finsetSum _ (fun k _ =>
      ((coord_gaussDdim_integrable_ext τ hτ k).const_mul (Q k)))
  have hpt : (fun v : Point n => linMult τ Q v)
      = fun v => (1 / (2 * τ)) * ((∑ k, v k * Q k) * gaussDdim τ v) := by
    funext v; simp only [linMult]; ring
  rw [hpt]; exact hd_int.const_mul _

/-! ###############################################################################
    ### 2. `integral_linMult_eq_zero` — the exact full-space zero integral (M1 oddness).
    ############################################################################### -/

/-- **★ `integral_linMult_eq_zero` — the LINEAR first-moment cancellation.**  `∫ v, linMult τ Q v = 0`
    for `τ > 0`.  Pure linearity over `GaussianMomentExtraction.gaussDdim_first_moment_zero` (each
    coordinate `∫ v, v_k · G_τ(v) = 0`), no new moment machinery.  The exact analogue of
    `integral_heatHessMult_eq_zero` for J4-1017's residual term.  NOT `a₁ = R/6`. -/
theorem integral_linMult_eq_zero (τ : ℝ) (hτ : 0 < τ) (Q : Point n) :
    ∫ v : Point n, linMult τ Q v = 0 := by
  have hpt : ∀ v : Point n, linMult τ Q v
      = (1 / (2 * τ)) * ∑ k, Q k * (gaussDdim τ v * v k) := by
    intro v
    simp only [linMult]
    have hs : (∑ k, v k * Q k) * gaussDdim τ v = ∑ k, Q k * (gaussDdim τ v * v k) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [show (∑ k, v k * Q k) / (2 * τ) * gaussDdim τ v
          = (1 / (2 * τ)) * ((∑ k, v k * Q k) * gaussDdim τ v) from by ring, hs]
  rw [integral_congr_ae (ae_of_all _ hpt), integral_const_mul]
  have hsum0 : ∫ v : Point n, ∑ k, Q k * (gaussDdim τ v * v k) = 0 := by
    rw [integral_finsetSum _ (fun k _ => (coord_gaussDdim_integrable_ext τ hτ k).const_mul (Q k))]
    exact Finset.sum_eq_zero (fun k _ => by
      rw [integral_const_mul, gaussDdim_first_moment_zero τ hτ k, mul_zero])
  rw [hsum0, mul_zero]

/-! ###############################################################################
    ### 3. The pointwise majorant and the τ-INDEPENDENT Lipschitz-weight payoff.
    ############################################################################### -/

/-- `|linMult τ Q v| ≤ (n·‖Q‖/(2τ))·‖v‖·G_τ(v)`. -/
theorem abs_linMult_le (τ : ℝ) (hτ : 0 < τ) (Q v : Point n) :
    |linMult τ Q v| ≤ ((n : ℝ) * ‖Q‖ / (2 * τ)) * ‖v‖ * gaussDdim τ v := by
  have hGnn : 0 ≤ gaussDdim τ v := gaussDdim_nonneg _ _
  have hτ2 : (0:ℝ) < 2 * τ := by positivity
  calc |linMult τ Q v| = |(∑ k, v k * Q k) / (2 * τ)| * gaussDdim τ v := by
        rw [linMult, abs_mul, abs_of_nonneg hGnn]
    _ = |∑ k, v k * Q k| / (2 * τ) * gaussDdim τ v := by
        rw [abs_div, abs_of_pos hτ2]
    _ ≤ ((n : ℝ) * ‖v‖ * ‖Q‖) / (2 * τ) * gaussDdim τ v := by
        have hle : |∑ k, v k * Q k| / (2 * τ) ≤ ((n : ℝ) * ‖v‖ * ‖Q‖) / (2 * τ) := by
          gcongr
          exact abs_dot_le' v Q
        exact mul_le_mul_of_nonneg_right hle hGnn
    _ = ((n : ℝ) * ‖Q‖ / (2 * τ)) * ‖v‖ * gaussDdim τ v := by ring

/-- **★ `integral_linMult_mul_lipschitz` — THE LINEAR-MOMENT LIPSCHITZ PAYOFF (τ-INDEPENDENT).**
    For `τ > 0`, `L ≥ 0`, and a weight `f : Point n → ℝ` with spatial Lipschitz modulus at the origin
    (`|f v − f 0| ≤ L·‖v‖`),
        `|∫ v, linMult τ Q v · f v| ≤ n²·L·‖Q‖`.
    The `f 0` part CANCELS (`integral_linMult_eq_zero`); the remainder is majorised by
    `(n‖Q‖L/(2τ))·‖v‖²·G_τ(v)` and integrated via the n-D 2nd norm moment (`pow_norm_mul_gauss_integral`
    at `k=2`, `ck=2`, via `oneD_absMoment2`), where the `τ` in the `1/(2τ)` prefactor cancels EXACTLY
    against the `O(τ)` growth of the moment — landing at a bound CONSTANT in `τ` (sympy-verified,
    `hcomp_g1_term1_combined_rate_check.py`).  Same proof shape as
    `HeatHessMoment.integral_heatHessMult_mul_lipschitz`.  NOT `a₁ = R/6`. -/
theorem integral_linMult_mul_lipschitz (τ : ℝ) (hτ : 0 < τ) (Q : Point n)
    (L : ℝ) (hL : 0 ≤ L) (f : Point n → ℝ) (hf : AEStronglyMeasurable f volume)
    (hlip : ∀ v : Point n, |f v - f 0| ≤ L * ‖v‖) :
    |∫ v : Point n, linMult τ Q v * f v| ≤ (n : ℝ) ^ 2 * L * ‖Q‖ := by
  have hQnn : 0 ≤ ‖Q‖ := norm_nonneg _
  set c2 : ℝ := (n : ℝ) * ‖Q‖ * L / (2 * τ) with hc2def
  have hc2nn : 0 ≤ c2 := by rw [hc2def]; positivity
  set D : Point n → ℝ := fun v => c2 * (‖v‖ ^ 2 * gaussDdim τ v) with hDdef
  have hD_int : Integrable D volume := by
    rw [hDdef]; exact (normPow_gauss_integrable 2 (by norm_num) τ hτ).const_mul _
  have hptbnd : ∀ v : Point n, |linMult τ Q v * (f v - f 0)| ≤ D v := by
    intro v
    have hGnn : 0 ≤ gaussDdim τ v := gaussDdim_nonneg _ _
    calc |linMult τ Q v * (f v - f 0)|
        = |linMult τ Q v| * |f v - f 0| := abs_mul _ _
      _ ≤ (((n : ℝ) * ‖Q‖ / (2 * τ)) * ‖v‖ * gaussDdim τ v) * (L * ‖v‖) :=
          mul_le_mul (abs_linMult_le τ hτ Q v) (hlip v) (abs_nonneg _)
            (by positivity)
      _ = D v := by rw [hDdef, hc2def]; ring
  have hmeas_diff : AEStronglyMeasurable (fun v : Point n => linMult τ Q v * (f v - f 0)) volume :=
    (linMult_integrable τ hτ Q).aestronglyMeasurable.mul (hf.sub aestronglyMeasurable_const)
  have hint_diff : Integrable (fun v : Point n => linMult τ Q v * (f v - f 0)) volume :=
    hD_int.mono' hmeas_diff (Filter.Eventually.of_forall (fun v => by
      rw [Real.norm_eq_abs]; exact hptbnd v))
  have hL_int : Integrable (fun v : Point n => linMult τ Q v) volume := linMult_integrable τ hτ Q
  have hsplit_int : ∫ v : Point n, linMult τ Q v * f v
      = ∫ v : Point n, linMult τ Q v * (f v - f 0) := by
    have hpt : (fun v : Point n => linMult τ Q v * f v)
        = fun v => linMult τ Q v * (f v - f 0) + f 0 * linMult τ Q v := by
      funext v; ring
    rw [hpt, integral_add hint_diff (hL_int.const_mul _), integral_const_mul,
        integral_linMult_eq_zero τ hτ Q, mul_zero, add_zero]
  rw [hsplit_int]
  have hstep1 : |∫ v : Point n, linMult τ Q v * (f v - f 0)| ≤ ∫ v : Point n, D v := by
    calc |∫ v : Point n, linMult τ Q v * (f v - f 0)|
        ≤ ∫ v : Point n, |linMult τ Q v * (f v - f 0)| := by
          have h := norm_integral_le_integral_norm (μ := (volume : Measure (Point n)))
            (fun v : Point n => linMult τ Q v * (f v - f 0))
          simpa only [Real.norm_eq_abs] using h
      _ ≤ ∫ v : Point n, D v :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall (fun v => abs_nonneg _))
            hD_int (Filter.Eventually.of_forall hptbnd)
  refine le_trans hstep1 ?_
  have hDval : ∫ v : Point n, D v = c2 * (∫ v : Point n, ‖v‖ ^ 2 * gaussDdim τ v) := by
    rw [hDdef, integral_const_mul]
  rw [hDval]
  have hm2 : ∫ v : Point n, ‖v‖ ^ 2 * gaussDdim τ v ≤ (n : ℝ) * 2 * τ := by
    have h := pow_norm_mul_gauss_integral (n := n) 2 (by norm_num) 1 one_pos τ hτ
      2 (by norm_num) (by simpa [one_mul] using oneD_absMoment2 τ hτ)
    have h2 : (Real.sqrt τ) ^ 2 = τ := Real.sq_sqrt hτ.le
    simpa [one_mul, Real.sqrt_one, h2] using h
  have hτne : τ ≠ 0 := hτ.ne'
  calc c2 * (∫ v : Point n, ‖v‖ ^ 2 * gaussDdim τ v)
      ≤ c2 * ((n : ℝ) * 2 * τ) := mul_le_mul_of_nonneg_left hm2 hc2nn
    _ = (n : ℝ) ^ 2 * L * ‖Q‖ := by
        rw [hc2def]; field_simp

/-! ###############################################################################
    ### 4. ★ THE G1 PAYOFF — the pre-`|·|` signed identity and the combined bound.
    ############################################################################### -/

/-- `heatHessMult τ p q · Amp` is integrable whenever `Amp` is Lipschitz-at-`0`
    (`Amp v = (Amp v − Amp 0) + Amp 0`, sum of the already-dominated centred piece and a constant
    multiple of `heatHessMult`). -/
theorem heatHessMult_mul_lipschitzAmp_integrable (τ : ℝ) (hτ : 0 < τ) (p q : Point n)
    (Amp : Point n → ℝ) (hAmp : AEStronglyMeasurable Amp volume)
    (L : ℝ) (hlip : ∀ v : Point n, |Amp v - Amp 0| ≤ L * ‖v‖) :
    Integrable (fun v : Point n => heatHessMult τ p q v * Amp v) volume := by
  have hHH_int : Integrable (fun v : Point n => heatHessMult τ p q v) volume :=
    heatHessMult_integrable τ hτ p q
  set C : ℝ := (n : ℝ) ^ 2 * ‖p‖ * ‖q‖ with hCdef
  set c3 : ℝ := L * C / (4 * τ ^ 2) with hc3def
  set c1 : ℝ := L * C / (2 * τ) with hc1def
  set D : Point n → ℝ := fun v => c3 * (‖v‖ ^ 3 * gaussDdim τ v) + c1 * (‖v‖ ^ 1 * gaussDdim τ v)
    with hDdef
  have hD_int : Integrable D volume := by
    rw [hDdef]
    exact ((normPow_gauss_integrable 3 (by norm_num) τ hτ).const_mul _).add
      ((normPow_gauss_integrable 1 (by norm_num) τ hτ).const_mul _)
  have hHHint_diff : Integrable (fun v : Point n => heatHessMult τ p q v * (Amp v - Amp 0))
      volume := by
    refine hD_int.mono' (hHH_int.aestronglyMeasurable.mul (hAmp.sub aestronglyMeasurable_const))
      (Filter.Eventually.of_forall (fun v => ?_))
    have hGnn : 0 ≤ gaussDdim τ v := gaussDdim_nonneg _ _
    rw [Real.norm_eq_abs]
    calc |heatHessMult τ p q v * (Amp v - Amp 0)|
        = |heatHessMult τ p q v| * |Amp v - Amp 0| := abs_mul _ _
      _ ≤ ((C) * ((‖v‖ ^ 2 / (4 * τ ^ 2) + 1 / (2 * τ)) * gaussDdim τ v)) * (L * ‖v‖) :=
          mul_le_mul (abs_heatHessMult_le τ hτ p q v) (hlip v) (abs_nonneg _)
            (mul_nonneg (by positivity) (mul_nonneg (by positivity) hGnn))
      _ = D v := by rw [hDdef, hc3def, hc1def, hCdef]; ring
  have hpt : (fun v : Point n => heatHessMult τ p q v * Amp v)
      = fun v => heatHessMult τ p q v * (Amp v - Amp 0) + Amp 0 * heatHessMult τ p q v := by
    funext v; ring
  rw [hpt]; exact hHHint_diff.add (hHH_int.const_mul _)

/-- `linMult τ Q · Amp` is integrable whenever `Amp` is Lipschitz-at-`0`. -/
theorem linMult_mul_lipschitzAmp_integrable (τ : ℝ) (hτ : 0 < τ) (Q : Point n)
    (Amp : Point n → ℝ) (hAmp : AEStronglyMeasurable Amp volume)
    (L : ℝ) (hlip : ∀ v : Point n, |Amp v - Amp 0| ≤ L * ‖v‖) :
    Integrable (fun v : Point n => linMult τ Q v * Amp v) volume := by
  have hL_int : Integrable (fun v : Point n => linMult τ Q v) volume := linMult_integrable τ hτ Q
  have hD_int : Integrable (fun v : Point n =>
      ((n : ℝ) * ‖Q‖ * L / (2 * τ)) * (‖v‖ ^ 2 * gaussDdim τ v)) volume :=
    (normPow_gauss_integrable 2 (by norm_num) τ hτ).const_mul _
  have hLint_diff : Integrable (fun v : Point n => linMult τ Q v * (Amp v - Amp 0)) volume := by
    refine hD_int.mono' (hL_int.aestronglyMeasurable.mul (hAmp.sub aestronglyMeasurable_const))
      (Filter.Eventually.of_forall (fun v => ?_))
    have hGnn : 0 ≤ gaussDdim τ v := gaussDdim_nonneg _ _
    rw [Real.norm_eq_abs]
    calc |linMult τ Q v * (Amp v - Amp 0)|
        = |linMult τ Q v| * |Amp v - Amp 0| := abs_mul _ _
      _ ≤ (((n : ℝ) * ‖Q‖ / (2 * τ)) * ‖v‖ * gaussDdim τ v) * (L * ‖v‖) :=
          mul_le_mul (abs_linMult_le τ hτ Q v) (hlip v) (abs_nonneg _)
            (mul_nonneg (by positivity) hGnn)
      _ = ((n : ℝ) * ‖Q‖ * L / (2 * τ)) * (‖v‖ ^ 2 * gaussDdim τ v) := by ring
  have hpt : (fun v : Point n => linMult τ Q v * Amp v)
      = fun v => linMult τ Q v * (Amp v - Amp 0) + Amp 0 * linMult τ Q v := by
    funext v; ring
  rw [hpt]; exact hLint_diff.add (hL_int.const_mul _)

/-- **★★ `hsMixed_gaussDdim_mul_amp_eq_diff` — THE PRE-`|·|` CANCELLATION EXPOSURE.**
    For `τ > 0`, chart-Jacobian jet fields `PI PJ Q : Point n`, and an amplitude weight `Amp`
    Lipschitz-at-`0` with modulus `L`,
        `∫ v, G_τ(v)·(hsMixed(τ,v,PI,PJ,Q)·Amp v)
            = (∫ v, heatHessMult τ PI PJ v · Amp v) − (∫ v, linMult τ Q v · Amp v)`,
    where `hsMixed(τ,v,PI,PJ,Q) := ⟨v,PI⟩⟨v,PJ⟩/(4τ²) − (⟨PI,PJ⟩+⟨v,Q⟩)/(2τ)` (J4-1017's literal
    scalar).  Derived via J4-1017's exact `ring` identity + `integral_sub` — NO `|·|` anywhere in this
    statement or its proof: this IS the literal "expose the cancellation before `|·|`" step G1
    demands, since `integral_heatHessMult_mul_lipschitz`/`integral_linMult_mul_lipschitz` (invoked next,
    at the FINAL step only) internally derive their OWN sign cancellation before bounding. NOT
    `a₁ = R/6`. -/
theorem hsMixed_gaussDdim_mul_amp_eq_diff (τ : ℝ) (hτ : 0 < τ) (PI PJ Q : Point n)
    (Amp : Point n → ℝ) (hAmp : AEStronglyMeasurable Amp volume)
    (L : ℝ) (hlip : ∀ v : Point n, |Amp v - Amp 0| ≤ L * ‖v‖) :
    ∫ v : Point n, gaussDdim τ v
        * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)
      = (∫ v : Point n, heatHessMult τ PI PJ v * Amp v)
          - (∫ v : Point n, linMult τ Q v * Amp v) := by
  have hpt1 : ∀ v : Point n, gaussDdim τ v
      * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
            - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)
      = heatHessMult τ PI PJ v * Amp v - linMult τ Q v * Amp v := by
    intro v
    have hid : (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
            - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)))
        * gaussDdim τ v
      = heatHessMult τ PI PJ v - linMult τ Q v := by
      simp only [heatHessMult, linMult]; ring
    calc gaussDdim τ v
        * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)
        = ((((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ))) * gaussDdim τ v) * Amp v := by
          ring
      _ = (heatHessMult τ PI PJ v - linMult τ Q v) * Amp v := by rw [hid]
      _ = heatHessMult τ PI PJ v * Amp v - linMult τ Q v * Amp v := by ring
  rw [integral_congr_ae (ae_of_all _ hpt1)]
  exact integral_sub (heatHessMult_mul_lipschitzAmp_integrable τ hτ PI PJ Amp hAmp L hlip)
    (linMult_mul_lipschitzAmp_integrable τ hτ Q Amp hAmp L hlip)

/-- **★★★ `hsMixed_gaussDdim_mul_amp_lipschitz_bound` — THE G1 PAYOFF.**  For `τ > 0`, chart-Jacobian
    jet fields `PI PJ Q : Point n`, and an amplitude weight `Amp` Lipschitz-at-`0` with modulus `L ≥ 0`
    (`AEStronglyMeasurable`), the FULL-SPACE `hsMixed`-weighted Gaussian integral is bounded by the
    combined SIGNED-THEN-BOUNDED estimate
        `|∫ v, G_τ(v)·(hsMixed(τ,v,PI,PJ,Q)·Amp v)|
            ≤ L·n³·‖PI‖·‖PJ‖·(16√2+1)/√τ + n²·L·‖Q‖`.
    Derived from `hsMixed_gaussDdim_mul_amp_eq_diff`'s pre-`|·|` signed identity by applying
    `integral_heatHessMult_mul_lipschitz` and `integral_linMult_mul_lipschitz` DIRECTLY to the two
    full-`Amp` integrals (each of which internally exposes its OWN sign cancellation before bounding),
    THEN the triangle inequality — `|·|` appears ONLY at the very last step, on the fully-assembled
    bound.  This is THE literal G1 gate deliverable (Sol `gpt-5.6-sol`, high, 2026-08-23: "GO … the
    required cancellation is exposed separately in each signed integral … applying the triangle
    inequality only after these rewrites does not destroy cancellation").  STILL FULL-SPACE ONLY — NOT
    yet wired to `nb`'s bounded IFT domain `S'` (that reconciliation, plus a `linMult` analogue of
    J4-1018's ball-tail bound, is SEPARATE, still-open work).  NOT `a₁ = R/6`. -/
theorem hsMixed_gaussDdim_mul_amp_lipschitz_bound (τ : ℝ) (hτ : 0 < τ) (PI PJ Q : Point n)
    (Amp : Point n → ℝ) (hAmp : AEStronglyMeasurable Amp volume)
    (L : ℝ) (hL : 0 ≤ L) (hlip : ∀ v : Point n, |Amp v - Amp 0| ≤ L * ‖v‖) :
    |∫ v : Point n, gaussDdim τ v
        * (((∑ k, v k * PI k) * (∑ k, v k * PJ k) / (4 * τ ^ 2)
              - ((∑ k, PI k * PJ k) + (∑ k, v k * Q k)) / (2 * τ)) * Amp v)|
      ≤ L * (n : ℝ) ^ 3 * ‖PI‖ * ‖PJ‖ * (16 * Real.sqrt 2 + 1) / Real.sqrt τ
          + (n : ℝ) ^ 2 * L * ‖Q‖ := by
  rw [hsMixed_gaussDdim_mul_amp_eq_diff τ hτ PI PJ Q Amp hAmp L hlip, sub_eq_add_neg]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg]
  exact add_le_add
    (integral_heatHessMult_mul_lipschitz τ hτ PI PJ L hL Amp hAmp hlip)
    (integral_linMult_mul_lipschitz τ hτ Q L hL Amp hAmp hlip)

end QIQTH.HCompNearCarryTerm1LipschitzCancellation

/-! ### Axiom audit (std-3 expected: propext, Classical.choice, Quot.sound). -/

section AxiomChecks
open QIQTH.HCompNearCarryTerm1LipschitzCancellation
#print axioms integral_linMult_eq_zero
#print axioms integral_linMult_mul_lipschitz
#print axioms hsMixed_gaussDdim_mul_amp_eq_diff
#print axioms hsMixed_gaussDdim_mul_amp_lipschitz_bound
end AxiomChecks
