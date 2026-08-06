/-
  TUniformFrozenAI — J4-309: the t-UNIFORM FROZEN approximate identity (the L2 residual wall).

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ⚠  HONEST FIREWALL.  THIS FILE IS **NOT** `a₁ = R/6` and proves NOTHING new about `R/6`.  It is a
  COMPOSITION / limit-plumbing brick.  No `sorry` (header prose excepted), no new axioms, no `:= True`,
  no vacuous / unsatisfiable hypothesis, no hypothesis equal to (or trivially yielding) the conclusion,
  no existing file edited.

  ══════════════════════════════════════════════════════════════════════════════════════════════════
  ## CONTEXT — the L2 residual of `LocUnifDerivConv`.

  `LocUnifDerivConv.hbdryLU_of_movingCorr_frozen` (J4-308) reduced the W1-free `hbdryLU` to TWO loc-unif
  inputs.  The moving side (L1 `movingCorr_tUniform`) is DONE.  The residual WALL (L2) is the t-UNIFORM
  FROZEN limit
      `hfroLU : TendstoLocallyUniformlyOn (fun m u => ∫ z, H (epsSeq m) 0 z * F u z 0)
                  (fun u => F u 0 0) atTop U`.
  The fixed-`u` limit is banked (`GateAnnulusSplit.chartImage_approx_identity_final` composed along
  `epsSeq`, cf. `MovingFBoundaryLim.frozenBoundary_tendsto`).  This file promotes it UNIFORMLY over the
  window `u ∈ [ta,tb]`.

  ## THE HONEST ROUTE (avoids re-opening the AI's internals).  With `W τ z := H τ 0 z`,
  `f u z := F u z 0`, `c := f u 0`, `M_m := ∫ z, W (ε_m) z`:
      `∫ W(ε_m)·f_u − c  =  ∫ W(ε_m)·(f_u − c)  +  c·(M_m − 1)`,
  and `∫ W(ε_m)·(f_u − c)  =  ∫_ball W·(f_u − c)  +  ∫_ballᶜ W·(f_u − c)`.  The three pieces:
    • the NEAR part `|∫_ball W·(f_u − c)| ≤ (∫_ball|W|)·(u-uniform modulus ε') ≤ CW·ε'` — the ball radius
      is the modulus radius `δ(ε')`, and the modulus is the JOINT continuity modulus (u-uniform, T2);
    • the FAR part `|∫_ballᶜ W·(f_u − c)| ≤ (2·Cf)·CW·(off-ball Gaussian tail)` — u-free (`|f_u − c| ≤ 2Cf`);
    • the MASS-DEFECT `|c·(M_m − 1)| ≤ Cf·|M_m − 1|` — u-free, `M_m → 1` is the AI at `f ≡ 1` (T1).
  Only the AI at `f ≡ 1` (u-free mass-one, T1) is re-used — the AI's ε-δ internals are NOT re-opened.

  ## WHAT THIS FILE LANDS.
    • (T1) `witnessMass_tendsto_one` — the AI at `f ≡ 1`, composed along `epsSeq`:  `∫ Wit(ε_m) 0 · → 1`.
    • (T2) `frozenModulus_uniform` — the u-uniform continuity modulus at `z = 0` from the FINAL joint
      continuity on the compact strip.
    • (T3) `frozenAI_tUniform` — the 3-piece split ⟹ `TendstoUniformlyOn (fun m u => ∫ W(ε_m)·f_u)
      (fun u => f_u 0) atTop (Icc ta tb)`.  Kernel-agnostic.
    • (T4) `frozenAI_locUnif` — the loc-unif form on an OPEN `U` (each compact `K ⊆ U` sits in a window).
    • (T5) `hbdryLU_W1free_of_frozen_locUnif` — L3 fed (L1's loc-unif + T4) ⟹ the exact `hbdryLU` slot.

  ⚠  STILL NOT `a₁ = R/6`.
-/
import QIQTH.LocUnifDerivConv
import QIQTH.MovingFBoundaryLim

open MeasureTheory Filter
open QIQTH.Curvature QIQTH.FlatHeatEquation QIQTH.HeatResidualBound QIQTH.ResidueBound
open QIQTH.LeviSeries QIQTH.TrueHeatKernel
open scoped Topology

namespace QIQTH.TUniformFrozenAI

variable {n : ℕ}

set_option maxHeartbeats 1600000

/-! ###############################################################################
    ### (T1) — the u-free MASS-ONE limit: the AI at `f ≡ 1`, sequenced along `epsSeq`.
    ############################################################################### -/

/-- **★★ (T1) `witnessMass_tendsto_one`.**  The witness MASS tends to `1` along `ε_m`:
        `Tendsto (fun m => ∫ z, vanVleckGatedWitness g gi hC hK S a b (ε_m) 0 z) atTop (𝓝 1)`.
    Route: `GateAnnulusSplit.chartImage_approx_identity_final` at the CONSTANT function `f ≡ 1` (whose
    F-facts are trivial: `measurable_const`, global bound `⟨1, _⟩`, `continuousAt_const`, and `f 0 = 1`)
    gives `Tendsto (fun τ => ∫ z, Wit τ 0 z · 1) (𝓝[>]0) (𝓝 1)`; composing with `ε_m → 0⁺`
    (`MovingFBoundaryLim.tendsto_comp_epsSeq`) and dropping the `·1` yields the `atTop` mass limit.
    This is the SOLE re-use of the AI in the L2 route (the ε-δ internals are NOT re-opened).  The
    hypothesis list is exactly the AI's geometry / gate / domination list — all satisfiable, NONE the
    conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem witnessMass_tendsto_one
    (g gi : Point n → Fin n → Fin n → ℝ)
    (hC : ∀ a b c, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => christoffel g gi a b c y))
    {K : Set (Point n)} (hK : IsCompact K) (h0Kmem : K ∈ 𝓝 (0 : Point n))
    (hg : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => g y a b))
    (hgi : ∀ a b, ContDiff ℝ (⊤ : WithTop ℕ∞) (fun y => gi y a b))
    (hgpos : ∀ v : Point n, 0 < Matrix.det (g v))
    (S : Point n → Set (Point n)) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hgdet0 : Matrix.det (g 0) = 1)
    (rS : ℝ) (hrS : 0 < rS)
    (hKball : Metric.ball (0 : Point n) rS ⊆ K)
    (hSact : ∀ z ∈ Metric.ball (0 : Point n) rS, (0 : Point n) ∈ S z)
    (hWslice : ∀ τ : ℝ,
      AEStronglyMeasurable
        (fun z => vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z) volume)
    (lam τ₀ CW : ℝ) (hlam : 0 < lam) (hτ₀ : 0 < τ₀) (hCW : 0 ≤ CW)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z,
      |vanVleckGatedWitness g gi hC hK S a b τ (0 : Point n) z| ≤ CW * gaussDdim (lam * τ) z) :
    Tendsto
      (fun m => ∫ z, vanVleckGatedWitness g gi hC hK S a b (epsSeq m) (0 : Point n) z)
      atTop (𝓝 (1 : ℝ)) := by
  obtain ⟨ρ, _hρ, hAI⟩ :=
    QIQTH.GateAnnulusSplit.chartImage_approx_identity_final
      g gi hC hK h0Kmem hg hgi hgpos S a b ha hab hgdet0
      (fun _ => (1 : ℝ)) measurable_const ⟨1, fun _ => by norm_num⟩ continuousAt_const
      rS hrS hKball hSact hWslice lam τ₀ CW hlam hτ₀ hCW hDom
  simpa only [mul_one] using QIQTH.MovingFBoundaryLim.tendsto_comp_epsSeq hAI

/-! ###############################################################################
    ### (T2) — the u-UNIFORM continuity modulus at `z = 0` (from joint continuity).
    ############################################################################### -/

/-- **★★ (T2) `frozenModulus_uniform`.**  The u-UNIFORM continuity modulus at `z = 0`.  From the JOINT
    continuity of the FINAL `0`-slice `F` on the compact strip `Icc ta tb ×ˢ closedBall 0 R`
    (Heine–Cantor ⟹ uniform continuity), for every `ε > 0` there is a SINGLE `δ > 0` (u-free) with
        `∀ u ∈ [ta,tb], ∀ z ∈ ball 0 δ, |F u z − F u 0| < ε`.
    Route: uniform continuity supplies a `t`-free modulus `δ₀`; the shift distance
    `dist ((u,z),(u,0)) = dist z 0 = ‖z‖`, so `δ := min δ₀ R` keeps `z ∈ closedBall 0 R` (the domain) and
    `‖z‖ < δ₀`.  Kernel-agnostic; `hcont` is the SAME satisfiable FINAL joint-continuity carry used by the
    B1 Heine sup.  NONE of the hypotheses is the conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem frozenModulus_uniform
    (F : ℝ → Point n → ℝ) (ta tb R : ℝ) (hR : 0 < R)
    (hcont : ContinuousOn (fun p : ℝ × Point n => F p.1 p.2)
      (Set.Icc ta tb ×ˢ Metric.closedBall (0 : Point n) R))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ u ∈ Set.Icc ta tb, ∀ z ∈ Metric.ball (0 : Point n) δ,
      |F u z - F u 0| < ε := by
  have hs : IsCompact (Set.Icc ta tb ×ˢ Metric.closedBall (0 : Point n) R) :=
    isCompact_Icc.prod (isCompact_closedBall (0 : Point n) R)
  have huc := hs.uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδprop⟩ := huc ε hε
  refine ⟨min δ R, lt_min hδ hR, ?_⟩
  intro u hu z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have hzR : z ∈ Metric.closedBall (0 : Point n) R := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt (lt_of_lt_of_le hz (min_le_right _ _))
  have h0R : (0 : Point n) ∈ Metric.closedBall (0 : Point n) R := by
    rw [Metric.mem_closedBall, dist_self]; exact hR.le
  have hpmem : (u, z) ∈ Set.Icc ta tb ×ˢ Metric.closedBall (0 : Point n) R :=
    Set.mem_prod.mpr ⟨hu, hzR⟩
  have hqmem : (u, (0 : Point n)) ∈ Set.Icc ta tb ×ˢ Metric.closedBall (0 : Point n) R :=
    Set.mem_prod.mpr ⟨hu, h0R⟩
  have hzδ : dist z (0 : Point n) < δ := by
    rw [dist_zero_right]; exact lt_of_lt_of_le hz (min_le_left _ _)
  have hdist : dist (u, z) (u, (0 : Point n)) < δ := by
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]; exact hzδ
  have hfin := hδprop (u, z) hpmem (u, (0 : Point n)) hqmem hdist
  rw [Real.dist_eq] at hfin
  exact hfin

/-! ###############################################################################
    ### (T3) — the u-UNIFORM FROZEN estimate (the 3-piece split).
    ############################################################################### -/

/-- **★★★ (T3) `frozenAI_tUniform`.**  THE u-UNIFORM FROZEN approximate identity.  The frozen witness
    pairing concentrates at the diagonal value UNIFORMLY over the window `u ∈ [ta,tb]`:
        `TendstoUniformlyOn (fun m u => ∫ z, W (ε_m) z · f u z) (fun u => f u 0) atTop [ta,tb]`,
    `W τ z = H τ 0 z` the witness slice at base `0`, `f u z = F u z 0` the source slice.
    Route (per fixed `ε`): pick the modulus radius `δ = δ(ε')` from the u-uniform modulus `hmod`
    (`ε' = ε/(3(CW+1))`) and split, for every `m` with the eventual facts and every `u`,
        `∫ W(ε_m)·f_u − f_u 0 = ∫ W(ε_m)·(f_u − f_u 0) + f_u 0·(∫ W(ε_m) − 1)`,
    then `∫ W·(f_u − f_u 0)` into `ball 0 δ` + `(ball 0 δ)ᶜ`:
      • NEAR `≤ (∫_ball|W|)·ε' ≤ CW·ε' < ε/3` (mass ≤ `CW`, modulus `hmod`);
      • FAR `≤ (2Cf)·CW·(off-ball Gaussian tail) < ε/3` (`|f_u − f_u 0| ≤ 2Cf`, tail → 0, u-free);
      • MASS-DEFECT `≤ Cf·|∫ W(ε_m) − 1| < ε/3` (u-free, `hmassone` = the AI at `f ≡ 1`).
    Kernel-agnostic.  `hmod` is satisfiable by (T2) `frozenModulus_uniform`, `hmassone` by (T1)
    `witnessMass_tendsto_one`; the mass/tail/domination are the window-uniform Levi envelope + witness
    domination.  NONE of the hypotheses is the conclusion.  ⚠ NOT `a₁ = R/6`. -/
theorem frozenAI_tUniform
    (W : ℝ → Point n → ℝ) (f : ℝ → Point n → ℝ)
    (lam CW Cf τ₀ ta tb : ℝ)
    (hlam : 0 < lam) (hCW : 0 ≤ CW) (hτ₀ : 0 < τ₀)
    (hWmeas : ∀ τ, AEStronglyMeasurable (W τ) volume)
    (hf_meas : ∀ u, AEStronglyMeasurable (f u) volume)
    (hf_bdd : ∀ u z, |f u z| ≤ Cf)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z, |W τ z| ≤ CW * gaussDdim (lam * τ) z)
    (hmass : ∀ᶠ m in atTop, ∫ z, |W (epsSeq m) z| ≤ CW)
    (hmassone : Tendsto (fun m => ∫ z, W (epsSeq m) z) atTop (𝓝 1))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.ball (0 : Point n) δ, |f u z - f u 0| < ε) :
    TendstoUniformlyOn
      (fun m u => ∫ z, W (epsSeq m) z * f u z)
      (fun u => f u 0) atTop (Set.Icc ta tb) := by
  have hcap : ∀ᶠ m in atTop, epsSeq m ≤ τ₀ := by
    have h := epsSeq_tendsto.eventually (Iic_mem_nhds hτ₀)
    filter_upwards [h] with m hm
    exact Set.mem_Iic.mp hm
  have hCW1 : (0 : ℝ) < CW + 1 := by linarith
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  have hε' : (0 : ℝ) < ε / (3 * (CW + 1)) := by positivity
  obtain ⟨δ, hδpos, hδprop⟩ := hmod (ε / (3 * (CW + 1))) hε'
  -- the (u-free) off-ball Gaussian tail along ε_m, at radius δ.
  have hc : Tendsto (fun τ : ℝ => lam * τ) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have h : Tendsto (fun τ : ℝ => lam * τ) (𝓝 (0 : ℝ)) (𝓝 (lam * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hscale : Tendsto (fun τ : ℝ => lam * τ) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hc, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact Set.mem_Ioi.mpr (mul_pos hlam (Set.mem_Ioi.mp hτ))
  have htailτ : Tendsto
      (fun τ => ∫ w in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (lam * τ) w)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (QIQTH.ChartImageApproxIdentity.gaussDdim_ballCompl_mass_tendsto_zero (n := n) δ hδpos).comp hscale
  have hGtail : Tendsto
      (fun m => ∫ w in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (lam * epsSeq m) w)
      atTop (𝓝 0) :=
    QIQTH.MovingFBoundaryLim.tendsto_comp_epsSeq htailτ
  have hub : Tendsto
      (fun m => (2 * Cf * CW) * ∫ w in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (lam * epsSeq m) w)
      atTop (𝓝 0) := by
    have h := hGtail.const_mul (2 * Cf * CW)
    simpa using h
  -- the (u-free) mass-defect along ε_m.
  have hdefect : Tendsto (fun m => Cf * |(∫ z, W (epsSeq m) z) - 1|) atTop (𝓝 0) := by
    have h0 : Tendsto (fun m => (∫ z, W (epsSeq m) z) - 1) atTop (𝓝 0) := by
      have := hmassone.sub_const 1; simpa using this
    have h1 := h0.abs
    have h2 := h1.const_mul Cf
    simpa using h2
  filter_upwards [hmass, hcap, hub.eventually (Iio_mem_nhds hε3),
    hdefect.eventually (Iio_mem_nhds hε3)] with m hmassm hcapm htailm hdefm
  have htailm' : (2 * Cf * CW)
      * ∫ w in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (lam * epsSeq m) w < ε / 3 :=
    Set.mem_Iio.mp htailm
  have hdefm' : Cf * |(∫ z, W (epsSeq m) z) - 1| < ε / 3 := Set.mem_Iio.mp hdefm
  have hτp : 0 < epsSeq m := epsSeq_pos m
  -- W(ε_m) globally integrable + |W| integrable.
  have hWint : Integrable (fun z => W (epsSeq m) z) volume := by
    refine Integrable.mono'
      ((gaussDdim_integrable (lam * epsSeq m) (mul_pos hlam hτp)).const_mul CW)
      (hWmeas _) (ae_of_all _ (fun z => ?_))
    rw [Real.norm_eq_abs]
    exact hDom (epsSeq m) hτp hcapm z
  have hWabsInt : Integrable (fun z => |W (epsSeq m) z|) volume := hWint.abs
  intro u hu
  -- integrability of the u-slice product and the centered product.
  have hInt_f : Integrable (fun z => W (epsSeq m) z * f u z) volume := by
    refine Integrable.mono'
      ((gaussDdim_integrable (lam * epsSeq m) (mul_pos hlam hτp)).const_mul (CW * Cf))
      ((hWmeas _).mul (hf_meas u)) (ae_of_all _ (fun z => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hDom (epsSeq m) hτp hcapm z
    calc |W (epsSeq m) z| * |f u z|
        ≤ (CW * gaussDdim (lam * epsSeq m) z) * Cf :=
          mul_le_mul h1 (hf_bdd u z) (abs_nonneg _) (mul_nonneg hCW (gaussDdim_nonneg _ _))
      _ = CW * Cf * gaussDdim (lam * epsSeq m) z := by ring
  have hInt_diff : Integrable (fun z => W (epsSeq m) z * (f u z - f u 0)) volume := by
    have h := hInt_f.sub (hWint.mul_const (f u 0))
    refine h.congr (ae_of_all _ (fun z => ?_))
    simp only [Pi.sub_apply]; ring
  -- the split identity.
  have key : (∫ z, W (epsSeq m) z * f u z) - f u 0
      = (∫ z, W (epsSeq m) z * (f u z - f u 0)) + f u 0 * ((∫ z, W (epsSeq m) z) - 1) := by
    have h1 : ∫ z, W (epsSeq m) z * (f u z - f u 0)
        = (∫ z, W (epsSeq m) z * f u z) - ∫ z, W (epsSeq m) z * f u 0 := by
      rw [← integral_sub hInt_f (hWint.mul_const (f u 0))]
      refine integral_congr_ae (ae_of_all _ (fun z => ?_)); ring
    rw [h1, integral_mul_const]; ring
  -- integral_add_compl split of the centered integral.
  have hDsplit : (∫ z, W (epsSeq m) z * (f u z - f u 0))
      = (∫ z in Metric.ball (0 : Point n) δ, W (epsSeq m) z * (f u z - f u 0))
      + (∫ z in (Metric.ball (0 : Point n) δ)ᶜ, W (epsSeq m) z * (f u z - f u 0)) :=
    (integral_add_compl measurableSet_ball hInt_diff).symm
  -- NEAR bound.
  have hnear : |∫ z in Metric.ball (0 : Point n) δ, W (epsSeq m) z * (f u z - f u 0)|
      ≤ (ε / (3 * (CW + 1))) * CW := by
    have hmaj : IntegrableOn (fun z => (ε / (3 * (CW + 1))) * |W (epsSeq m) z|)
        (Metric.ball (0 : Point n) δ) volume :=
      (hWabsInt.const_mul (ε / (3 * (CW + 1)))).integrableOn
    have hbound :
        |∫ z in Metric.ball (0 : Point n) δ, W (epsSeq m) z * (f u z - f u 0)|
          ≤ (ε / (3 * (CW + 1))) * ∫ z in Metric.ball (0 : Point n) δ, |W (epsSeq m) z| := by
      rw [← Real.norm_eq_abs]
      calc ‖∫ z in Metric.ball (0 : Point n) δ, W (epsSeq m) z * (f u z - f u 0)‖
          ≤ ∫ z in Metric.ball (0 : Point n) δ, ‖W (epsSeq m) z * (f u z - f u 0)‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ z in Metric.ball (0 : Point n) δ, (ε / (3 * (CW + 1))) * |W (epsSeq m) z| := by
            refine integral_mono_of_nonneg (ae_of_all _ (fun z => norm_nonneg _)) hmaj ?_
            refine (ae_restrict_iff' measurableSet_ball).mpr (ae_of_all _ (fun z hz => ?_))
            simp only [Real.norm_eq_abs, abs_mul]
            have hlt := le_of_lt (hδprop u hu z hz)
            calc |W (epsSeq m) z| * |f u z - f u 0|
                ≤ |W (epsSeq m) z| * (ε / (3 * (CW + 1))) :=
                  mul_le_mul_of_nonneg_left hlt (abs_nonneg _)
              _ = (ε / (3 * (CW + 1))) * |W (epsSeq m) z| := by ring
        _ = (ε / (3 * (CW + 1))) * ∫ z in Metric.ball (0 : Point n) δ, |W (epsSeq m) z| := by
            rw [integral_const_mul]
    have hballmass : (∫ z in Metric.ball (0 : Point n) δ, |W (epsSeq m) z|) ≤ CW :=
      le_trans (setIntegral_le_integral hWabsInt (ae_of_all _ (fun z => abs_nonneg _))) hmassm
    calc |∫ z in Metric.ball (0 : Point n) δ, W (epsSeq m) z * (f u z - f u 0)|
        ≤ (ε / (3 * (CW + 1))) * ∫ z in Metric.ball (0 : Point n) δ, |W (epsSeq m) z| := hbound
      _ ≤ (ε / (3 * (CW + 1))) * CW :=
          mul_le_mul_of_nonneg_left hballmass (le_of_lt hε')
  -- FAR bound.
  have hfar : |∫ z in (Metric.ball (0 : Point n) δ)ᶜ, W (epsSeq m) z * (f u z - f u 0)|
      ≤ (2 * Cf * CW) * ∫ w in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (lam * epsSeq m) w := by
    have hgint : IntegrableOn (fun z : Point n => (2 * Cf * CW) * gaussDdim (lam * epsSeq m) z)
        (Metric.ball (0 : Point n) δ)ᶜ volume :=
      ((gaussDdim_integrable (lam * epsSeq m) (mul_pos hlam hτp)).const_mul (2 * Cf * CW)).integrableOn
    calc |∫ z in (Metric.ball (0 : Point n) δ)ᶜ, W (epsSeq m) z * (f u z - f u 0)|
        ≤ ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, |W (epsSeq m) z * (f u z - f u 0)| := by
          have := norm_integral_le_integral_norm
            (μ := volume.restrict (Metric.ball (0 : Point n) δ)ᶜ)
            (f := fun z => W (epsSeq m) z * (f u z - f u 0))
          simpa only [Real.norm_eq_abs] using this
      _ ≤ ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, (2 * Cf * CW) * gaussDdim (lam * epsSeq m) z := by
          refine integral_mono_of_nonneg (ae_of_all _ (fun z => abs_nonneg _)) hgint ?_
          refine ae_of_all _ (fun z => ?_)
          dsimp only
          rw [abs_mul]
          have h1 := hDom (epsSeq m) hτp hcapm z
          have h2 : |f u z - f u 0| ≤ 2 * Cf := by
            calc |f u z - f u 0| ≤ |f u z| + |f u 0| := abs_sub _ _
              _ ≤ Cf + Cf := add_le_add (hf_bdd u z) (hf_bdd u 0)
              _ = 2 * Cf := by ring
          have hg0 := gaussDdim_nonneg (lam * epsSeq m) z
          calc |W (epsSeq m) z| * |f u z - f u 0|
              ≤ (CW * gaussDdim (lam * epsSeq m) z) * (2 * Cf) :=
                mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hCW hg0)
            _ = (2 * Cf * CW) * gaussDdim (lam * epsSeq m) z := by ring
      _ = (2 * Cf * CW) * ∫ z in (Metric.ball (0 : Point n) δ)ᶜ, gaussDdim (lam * epsSeq m) z := by
          rw [integral_const_mul]
  -- recombine (3ε).
  rw [Real.dist_eq, abs_sub_comm, key]
  have hbnd1 : (ε / (3 * (CW + 1))) * CW < ε / 3 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0:ℝ) < 3 * (CW + 1))]
    nlinarith [hε, hCW]
  have hnear' : |∫ z in Metric.ball (0 : Point n) δ, W (epsSeq m) z * (f u z - f u 0)| < ε / 3 :=
    lt_of_le_of_lt hnear hbnd1
  have hfar' : |∫ z in (Metric.ball (0 : Point n) δ)ᶜ, W (epsSeq m) z * (f u z - f u 0)| < ε / 3 :=
    lt_of_le_of_lt hfar htailm'
  calc |(∫ z, W (epsSeq m) z * (f u z - f u 0)) + f u 0 * ((∫ z, W (epsSeq m) z) - 1)|
      ≤ |∫ z, W (epsSeq m) z * (f u z - f u 0)| + |f u 0 * ((∫ z, W (epsSeq m) z) - 1)| :=
        abs_add_le _ _
    _ ≤ (|∫ z in Metric.ball (0 : Point n) δ, W (epsSeq m) z * (f u z - f u 0)|
          + |∫ z in (Metric.ball (0 : Point n) δ)ᶜ, W (epsSeq m) z * (f u z - f u 0)|)
        + Cf * |(∫ z, W (epsSeq m) z) - 1| := by
        refine add_le_add ?_ ?_
        · rw [hDsplit]; exact abs_add_le _ _
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hf_bdd u 0) (abs_nonneg _)
    _ < ε := by linarith [hnear', hfar', hdefm']

/-! ###############################################################################
    ### (T4) — the LOC-UNIF form on an open, window-contained `U`.
    ############################################################################### -/

/-- **★★★ (T4) `frozenAI_locUnif`.**  The LOCALLY-UNIFORM version of (T3): if the (bounded) time set `U`
    sits inside a compact window `[ta,tb]` (`hUsub : U ⊆ Icc ta tb`) on which the (T3) hypotheses hold,
    then the frozen witness pairing converges to the diagonal value LOCALLY UNIFORMLY on `U`:
        `TendstoLocallyUniformlyOn (fun m u => ∫ z, W (ε_m) z · f u z) (fun u => f u 0) atTop U`.
    Route: (T3) gives `TendstoUniformlyOn` on `[ta,tb]`; `.mono hUsub` restricts to `U`, and
    `TendstoUniformlyOn.tendstoLocallyUniformlyOn` promotes.  (The physical boundary set — the open time
    interval `(t₁,t₂)` — is bounded and contained in a closed window `[t₁,t₂]` where the FINAL `0`-slice
    is jointly continuous, so `hUsub` is satisfiable.)  ⚠ NOT `a₁ = R/6`. -/
theorem frozenAI_locUnif
    (W : ℝ → Point n → ℝ) (f : ℝ → Point n → ℝ) (U : Set ℝ)
    (lam CW Cf τ₀ ta tb : ℝ)
    (hlam : 0 < lam) (hCW : 0 ≤ CW) (hτ₀ : 0 < τ₀)
    (hWmeas : ∀ τ, AEStronglyMeasurable (W τ) volume)
    (hf_meas : ∀ u, AEStronglyMeasurable (f u) volume)
    (hf_bdd : ∀ u z, |f u z| ≤ Cf)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z, |W τ z| ≤ CW * gaussDdim (lam * τ) z)
    (hmass : ∀ᶠ m in atTop, ∫ z, |W (epsSeq m) z| ≤ CW)
    (hmassone : Tendsto (fun m => ∫ z, W (epsSeq m) z) atTop (𝓝 1))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.ball (0 : Point n) δ, |f u z - f u 0| < ε)
    (hUsub : U ⊆ Set.Icc ta tb) :
    TendstoLocallyUniformlyOn
      (fun m u => ∫ z, W (epsSeq m) z * f u z)
      (fun u => f u 0) atTop U := by
  have hT3 := frozenAI_tUniform W f lam CW Cf τ₀ ta tb hlam hCW hτ₀
    hWmeas hf_meas hf_bdd hDom hmass hmassone hmod
  exact (hT3.mono hUsub).tendstoLocallyUniformlyOn

/-! ###############################################################################
    ### (T5) — THE W1-FREE `hbdryLU` SLOT: L3 fed with L1's loc-unif + (T4).
    ############################################################################### -/

/-- **★★★ (T5) `hbdryLU_W1free_of_frozen_locUnif`.**  THE W1-free `hbdryLU` slot assembled: feed
    `LocUnifDerivConv.hbdryLU_of_movingCorr_frozen` (L3) with the carried moving-side loc-unif `hmovLU`
    (L1's output, → 0 loc-unif) AND the FROZEN loc-unif produced by (T4) at `W τ z := H τ 0 z`,
    `f u z := F u z 0`.  Concludes EXACTLY the `derivConv_of_data` slot
        `hbdryLUTarget H F U = TendstoLocallyUniformlyOn (fun m u => BoundaryTrunc H F m u)
              (fun u => F u 0 0) atTop U`.
    All frozen-side hypotheses are the (T3)/(T4) satisfiable list at the `0`-based witness slice and the
    `0`-slice source (mass/domination = witness envelope; `hmassone` = (T1); `hmod` = (T2); `hf_bdd` =
    the window envelope); `hmovLU` is L1's genuine lower ingredient (→ 0, NOT the conclusion), and
    `hUsub : U ⊆ [ta,tb]` places the bounded time set in the continuity window.  NONE is the conclusion.
    ⚠ NOT `a₁ = R/6`. -/
theorem hbdryLU_W1free_of_frozen_locUnif
    (H F : ℝ → Point n → Point n → ℝ) (U : Set ℝ)
    (lam CW Cf τ₀ ta tb : ℝ)
    (hlam : 0 < lam) (hCW : 0 ≤ CW) (hτ₀ : 0 < τ₀)
    (hWmeas : ∀ τ, AEStronglyMeasurable (fun z => H τ (0 : Point n) z) volume)
    (hf_meas : ∀ u, AEStronglyMeasurable (fun z => F u z (0 : Point n)) volume)
    (hf_bdd : ∀ u z, |F u z (0 : Point n)| ≤ Cf)
    (hDom : ∀ τ, 0 < τ → τ ≤ τ₀ → ∀ z,
      |H τ (0 : Point n) z| ≤ CW * gaussDdim (lam * τ) z)
    (hmass : ∀ᶠ m in atTop, ∫ z, |H (epsSeq m) (0 : Point n) z| ≤ CW)
    (hmassone : Tendsto (fun m => ∫ z, H (epsSeq m) (0 : Point n) z) atTop (𝓝 1))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ u ∈ Set.Icc ta tb,
        ∀ z ∈ Metric.ball (0 : Point n) δ,
          |F u z (0 : Point n) - F u (0 : Point n) (0 : Point n)| < ε)
    (hUsub : U ⊆ Set.Icc ta tb)
    (hmovLU : TendstoLocallyUniformlyOn
        (fun m u => BoundaryTrunc H F m u - ∫ z, H (epsSeq m) (0 : Point n) z * F u z (0 : Point n))
        (fun _ => (0 : ℝ)) atTop U) :
    QIQTH.LocUnifDerivConv.hbdryLUTarget H F U := by
  have hfroLU := frozenAI_locUnif
    (fun τ z => H τ (0 : Point n) z) (fun u z => F u z (0 : Point n)) U
    lam CW Cf τ₀ ta tb hlam hCW hτ₀ hWmeas hf_meas hf_bdd hDom hmass hmassone hmod hUsub
  exact QIQTH.LocUnifDerivConv.hbdryLU_of_movingCorr_frozen H F U hmovLU hfroLU

end QIQTH.TUniformFrozenAI

section AxiomChecks
open QIQTH.TUniformFrozenAI
#print axioms witnessMass_tendsto_one
#print axioms frozenModulus_uniform
#print axioms frozenAI_tUniform
#print axioms frozenAI_locUnif
#print axioms hbdryLU_W1free_of_frozen_locUnif
end AxiomChecks
